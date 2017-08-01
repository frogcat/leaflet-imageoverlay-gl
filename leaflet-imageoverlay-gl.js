(function() {

  var Delaunator = (function() {

    // https://github.com/mapbox/delaunator/tree/v1.0.3

    function Delaunator(points, getX, getY) {

      if (!getX) getX = defaultGetX;
      if (!getY) getY = defaultGetY;

      var minX = Infinity;
      var minY = Infinity;
      var maxX = -Infinity;
      var maxY = -Infinity;

      var coords = this.coords = [];
      var ids = this.ids = new Uint32Array(points.length);

      for (var i = 0; i < points.length; i++) {
        var p = points[i];
        var x = getX(p);
        var y = getY(p);
        ids[i] = i;
        coords[2 * i] = x;
        coords[2 * i + 1] = y;
        if (x < minX) minX = x;
        if (y < minY) minY = y;
        if (x > maxX) maxX = x;
        if (y > maxY) maxY = y;
      }

      var cx = (minX + maxX) / 2;
      var cy = (minY + maxY) / 2;

      var minDist = Infinity;
      var i0, i1, i2;

      // pick a seed point close to the centroid
      for (i = 0; i < points.length; i++) {
        var d = dist(cx, cy, coords[2 * i], coords[2 * i + 1]);
        if (d < minDist) {
          i0 = i;
          minDist = d;
        }
      }

      minDist = Infinity;

      // find the point closest to the seed
      for (i = 0; i < points.length; i++) {
        if (i === i0) continue;
        d = dist(coords[2 * i0], coords[2 * i0 + 1], coords[2 * i], coords[2 * i + 1]);
        if (d < minDist && d > 0) {
          i1 = i;
          minDist = d;
        }
      }

      var minRadius = Infinity;

      // find the third point which forms the smallest circumcircle with the first two
      for (i = 0; i < points.length; i++) {
        if (i === i0 || i === i1) continue;

        var r = circumradius(
          coords[2 * i0], coords[2 * i0 + 1],
          coords[2 * i1], coords[2 * i1 + 1],
          coords[2 * i], coords[2 * i + 1]);

        if (r < minRadius) {
          i2 = i;
          minRadius = r;
        }
      }

      if (minRadius === Infinity) {
        throw new Error('No Delaunay triangulation exists for this input.');
      }

      // swap the order of the seed points for counter-clockwise orientation
      if (area(coords[2 * i0], coords[2 * i0 + 1],
          coords[2 * i1], coords[2 * i1 + 1],
          coords[2 * i2], coords[2 * i2 + 1]) < 0) {

        var tmp = i1;
        i1 = i2;
        i2 = tmp;
      }

      var i0x = coords[2 * i0];
      var i0y = coords[2 * i0 + 1];
      var i1x = coords[2 * i1];
      var i1y = coords[2 * i1 + 1];
      var i2x = coords[2 * i2];
      var i2y = coords[2 * i2 + 1];

      var center = circumcenter(i0x, i0y, i1x, i1y, i2x, i2y);
      this._cx = center.x;
      this._cy = center.y;

      // sort the points by distance from the seed triangle circumcenter
      quicksort(ids, coords, 0, ids.length - 1, center.x, center.y);

      // initialize a hash table for storing edges of the advancing convex hull
      this._hashSize = Math.ceil(Math.sqrt(points.length));
      this._hash = [];
      for (i = 0; i < this._hashSize; i++) this._hash[i] = null;

      // initialize a circular doubly-linked list that will hold an advancing convex hull
      var e = this.hull = insertNode(coords, i0);
      this._hashEdge(e);
      e.t = 0;
      e = insertNode(coords, i1, e);
      this._hashEdge(e);
      e.t = 1;
      e = insertNode(coords, i2, e);
      this._hashEdge(e);
      e.t = 2;

      var maxTriangles = 2 * points.length - 5;
      var triangles = this.triangles = new Uint32Array(maxTriangles * 3);
      var halfedges = this.halfedges = new Int32Array(maxTriangles * 3);

      this.trianglesLen = 0;

      this._addTriangle(i0, i1, i2, -1, -1, -1);

      var xp, yp;
      for (var k = 0; k < ids.length; k++) {
        i = ids[k];
        x = coords[2 * i];
        y = coords[2 * i + 1];

        // skip duplicate points
        if (x === xp && y === yp) continue;
        xp = x;
        yp = y;

        // skip seed triangle points
        if ((x === i0x && y === i0y) ||
          (x === i1x && y === i1y) ||
          (x === i2x && y === i2y)) continue;

        // find a visible edge on the convex hull using edge hash
        var startKey = this._hashKey(x, y);
        var key = startKey;
        var start;
        do {
          start = this._hash[key];
          key = (key + 1) % this._hashSize;
        } while ((!start || start.removed) && key !== startKey);

        e = start;
        while (area(x, y, e.x, e.y, e.next.x, e.next.y) >= 0) {
          e = e.next;
          if (e === start) {
            throw new Error('Something is wrong with the input points.');
          }
        }

        var walkBack = e === start;

        // add the first triangle from the point
        var t = this._addTriangle(e.i, i, e.next.i, -1, -1, e.t);

        e.t = t; // keep track of boundary triangles on the hull
        e = insertNode(coords, i, e);

        // recursively flip triangles from the point until they satisfy the Delaunay condition
        e.t = this._legalize(t + 2);

        // walk forward through the hull, adding more triangles and flipping recursively
        var q = e.next;
        while (area(x, y, q.x, q.y, q.next.x, q.next.y) < 0) {

          t = this._addTriangle(q.i, i, q.next.i, q.prev.t, -1, q.t);

          q.prev.t = this._legalize(t + 2);

          this.hull = removeNode(q);
          q = q.next;
        }

        if (walkBack) {
          // walk backward from the other side, adding more triangles and flipping
          q = e.prev;
          while (area(x, y, q.prev.x, q.prev.y, q.x, q.y) < 0) {

            t = this._addTriangle(q.prev.i, i, q.i, -1, q.t, q.prev.t);

            this._legalize(t + 2);

            q.prev.t = t;
            this.hull = removeNode(q);
            q = q.prev;
          }
        }

        // save the two new edges in the hash table
        this._hashEdge(e);
        this._hashEdge(e.prev);
      }

      // trim typed triangle mesh arrays
      this.triangles = triangles.subarray(0, this.trianglesLen);
      this.halfedges = halfedges.subarray(0, this.trianglesLen);
    }

    Delaunator.prototype = {

      _hashEdge: function(e) {
        this._hash[this._hashKey(e.x, e.y)] = e;
      },

      _hashKey: function(x, y) {
        var dx = x - this._cx;
        var dy = y - this._cy;
        // use pseudo-angle: a measure that monotonically increases
        // with real angle, but doesn't require expensive trigonometry
        var p = 1 - dx / (Math.abs(dx) + Math.abs(dy));
        return Math.floor((2 + (dy < 0 ? -p : p)) / 4 * this._hashSize);
      },

      _legalize: function(a) {
        var triangles = this.triangles;
        var coords = this.coords;
        var halfedges = this.halfedges;

        var b = halfedges[a];

        var a0 = a - a % 3;
        var b0 = b - b % 3;

        var al = a0 + (a + 1) % 3;
        var ar = a0 + (a + 2) % 3;
        var br = b0 + (b + 1) % 3;
        var bl = b0 + (b + 2) % 3;

        var p0 = triangles[ar];
        var pr = triangles[a];
        var pl = triangles[al];
        var p1 = triangles[bl];

        var illegal = inCircle(
          coords[2 * p0], coords[2 * p0 + 1],
          coords[2 * pr], coords[2 * pr + 1],
          coords[2 * pl], coords[2 * pl + 1],
          coords[2 * p1], coords[2 * p1 + 1]);

        if (illegal) {
          triangles[a] = p1;
          triangles[b] = p0;

          this._link(a, halfedges[bl]);
          this._link(b, halfedges[ar]);
          this._link(ar, bl);

          this._legalize(a);
          return this._legalize(br);
        }

        return ar;
      },

      _link: function(a, b) {
        this.halfedges[a] = b;
        if (b !== -1) this.halfedges[b] = a;
      },

      // add a new triangle given vertex indices and adjacent half-edge ids
      _addTriangle: function(i0, i1, i2, a, b, c) {
        var t = this.trianglesLen;

        this.triangles[t] = i0;
        this.triangles[t + 1] = i1;
        this.triangles[t + 2] = i2;

        this._link(t, a);
        this._link(t + 1, b);
        this._link(t + 2, c);

        this.trianglesLen += 3;

        return t;
      }
    };

    function dist(ax, ay, bx, by) {
      var dx = ax - bx;
      var dy = ay - by;
      return dx * dx + dy * dy;
    }

    function area(px, py, qx, qy, rx, ry) {
      return (qy - py) * (rx - qx) - (qx - px) * (ry - qy);
    }

    function inCircle(ax, ay, bx, by, cx, cy, px, py) {
      ax -= px;
      ay -= py;
      bx -= px;
      by -= py;
      cx -= px;
      cy -= py;

      var ap = ax * ax + ay * ay;
      var bp = bx * bx + by * by;
      var cp = cx * cx + cy * cy;

      var det = ax * (by * cp - bp * cy) -
        ay * (bx * cp - bp * cx) +
        ap * (bx * cy - by * cx);

      return det < 0;
    }

    function circumradius(ax, ay, bx, by, cx, cy) {
      bx -= ax;
      by -= ay;
      cx -= ax;
      cy -= ay;

      var bl = bx * bx + by * by;
      var cl = cx * cx + cy * cy;

      if (bl === 0 || cl === 0) return Infinity;

      var d = bx * cy - by * cx;
      if (d === 0) return Infinity;

      var x = (cy * bl - by * cl) * 0.5 / d;
      var y = (bx * cl - cx * bl) * 0.5 / d;

      return x * x + y * y;
    }

    function circumcenter(ax, ay, bx, by, cx, cy) {
      bx -= ax;
      by -= ay;
      cx -= ax;
      cy -= ay;

      var bl = bx * bx + by * by;
      var cl = cx * cx + cy * cy;

      var d = bx * cy - by * cx;

      var x = (cy * bl - by * cl) * 0.5 / d;
      var y = (bx * cl - cx * bl) * 0.5 / d;

      return {
        x: ax + x,
        y: ay + y
      };
    }

    // create a new node in a doubly linked list
    function insertNode(coords, i, prev) {
      var node = {
        i: i,
        x: coords[2 * i],
        y: coords[2 * i + 1],
        t: 0,
        prev: null,
        next: null,
        removed: false
      };

      if (!prev) {
        node.prev = node;
        node.next = node;

      } else {
        node.next = prev.next;
        node.prev = prev;
        prev.next.prev = node;
        prev.next = node;
      }
      return node;
    }

    function removeNode(node) {
      node.prev.next = node.next;
      node.next.prev = node.prev;
      node.removed = true;
      return node.prev;
    }

    function quicksort(ids, coords, left, right, cx, cy) {
      var i, j, temp;

      if (right - left <= 20) {
        for (i = left + 1; i <= right; i++) {
          temp = ids[i];
          j = i - 1;
          while (j >= left && compare(coords, ids[j], temp, cx, cy) > 0) ids[j + 1] = ids[j--];
          ids[j + 1] = temp;
        }
      } else {
        var median = (left + right) >> 1;
        i = left + 1;
        j = right;
        swap(ids, median, i);
        if (compare(coords, ids[left], ids[right], cx, cy) > 0) swap(ids, left, right);
        if (compare(coords, ids[i], ids[right], cx, cy) > 0) swap(ids, i, right);
        if (compare(coords, ids[left], ids[i], cx, cy) > 0) swap(ids, left, i);

        temp = ids[i];
        while (true) {
          do i++; while (compare(coords, ids[i], temp, cx, cy) < 0);
          do j--; while (compare(coords, ids[j], temp, cx, cy) > 0);
          if (j < i) break;
          swap(ids, i, j);
        }
        ids[left + 1] = ids[j];
        ids[j] = temp;

        if (right - i + 1 >= j - left) {
          quicksort(ids, coords, i, right, cx, cy);
          quicksort(ids, coords, left, j - 1, cx, cy);
        } else {
          quicksort(ids, coords, left, j - 1, cx, cy);
          quicksort(ids, coords, i, right, cx, cy);
        }
      }
    }

    function compare(coords, i, j, cx, cy) {
      var d1 = dist(coords[2 * i], coords[2 * i + 1], cx, cy);
      var d2 = dist(coords[2 * j], coords[2 * j + 1], cx, cy);
      return (d1 - d2) || (coords[2 * i] - coords[2 * j]) || (coords[2 * i + 1] - coords[2 * j + 1]);
    }

    function swap(arr, i, j) {
      var tmp = arr[i];
      arr[i] = arr[j];
      arr[j] = tmp;
    }

    function defaultGetX(p) {
      return p[0];
    }

    function defaultGetY(p) {
      return p[1];
    }

    return Delaunator;
  })();

  function multiply(a, b) {
    return [
      a[0] * b[0] + a[3] * b[1] + a[6] * b[2],
      a[1] * b[0] + a[4] * b[1] + a[7] * b[2],
      a[2] * b[0] + a[5] * b[1] + a[8] * b[2],
      a[0] * b[3] + a[3] * b[4] + a[6] * b[5],
      a[1] * b[3] + a[4] * b[4] + a[7] * b[5],
      a[2] * b[3] + a[5] * b[4] + a[8] * b[5],
      a[0] * b[6] + a[3] * b[7] + a[6] * b[8],
      a[1] * b[6] + a[4] * b[7] + a[7] * b[8],
      a[2] * b[6] + a[5] * b[7] + a[8] * b[8]
    ];
  }

  function inverse(a) {
    var det = a[0] * a[4] * a[8] + a[3] * a[7] * a[2] + a[6] * a[1] * a[5] -
      a[0] * a[7] * a[5] - a[6] * a[4] * a[2] - a[3] * a[1] * a[8];
    return [
      (a[4] * a[8] - a[7] * a[5]) / det,
      (a[7] * a[2] - a[1] * a[8]) / det,
      (a[1] * a[5] - a[4] * a[2]) / det,
      (a[6] * a[5] - a[3] * a[8]) / det,
      (a[0] * a[8] - a[6] * a[2]) / det,
      (a[3] * a[2] - a[0] * a[5]) / det,
      (a[3] * a[7] - a[6] * a[4]) / det,
      (a[6] * a[1] - a[0] * a[7]) / det,
      (a[0] * a[4] - a[1] * a[3]) / det
    ];
  }

  L.ImageOverlay.GL = L.ImageOverlay.extend({
    options: {
      opacity: 1.0,
      vertexShader: "attribute vec2 xy;attribute vec2 uv;varying vec2 a;" +
        "void main(){gl_Position=vec4(xy,0,1); a=uv;}",
      fragmentShader: "precision mediump float;uniform sampler2D image;varying vec2 a;" +
        "void main(){gl_FragColor=texture2D(image,a);}",
      interactive: false
    },
    initialize: function(url, groundControlPoints, options) {
      this._url = url;
      this._groundControlPoints = groundControlPoints;
      this._update();
      L.Util.setOptions(this, options);
    },
    _initImage: function() {
      var canvas = this._image = document.createElement("canvas");
      this.getPane().appendChild(canvas);
      this._gl = canvas.getContext('webgl') || canvas.getContext('experimental-webgl');
      var img = this._img = new Image();
      this._ready = false;
      img.crossOrigin = "anonymous";
      var that = this;
      img.onload = function() {
        that._initProgram();
        that._initHandler();
        that._update();
        that._ready = true;
        that._reset();
      };
      img.src = this._url;
    },
    _initProgram: function() {
      var gl = this._gl;
      var vs = gl.createShader(gl.VERTEX_SHADER);
      gl.shaderSource(vs, this.options.vertexShader);
      gl.compileShader(vs);
      var fs = gl.createShader(gl.FRAGMENT_SHADER);
      gl.shaderSource(fs, this.options.fragmentShader);
      gl.compileShader(fs);
      var pg = this._pg = gl.createProgram();
      gl.attachShader(pg, vs);
      gl.attachShader(pg, fs);
      gl.linkProgram(pg);
      if (gl.getProgramParameter(pg, gl.LINK_STATUS)) {
        gl.useProgram(pg);
      } else {
        console.log(gl.getProgramInfoLog(pg));
      }
    },
    _initHandler: function() {
      if (this.options.interactive !== true) return;
      this.on("click", function(event) {
        var p = this.latLngToTexturePoint(event.latlng);
        if (p) {
          var q = [p.x, p.y, event.latlng.lng, event.latlng.lat];
          this._groundControlPoints.push(q);
          this._update();
          this._addMarker(q, true);
          this._reset();
        }
      }, this);
      this._groundControlPoints.forEach(function(p, i) {
        this._addMarker(p, i > 3);
      }, this);
    },
    _addMarker: function(p, removable) {
      var marker = L.marker(L.latLng(p[3], p[2]), {
        draggable: true
      }).addTo(this._map);
      marker._target = p;
      marker.on("move", function(event) {
        marker._target[2] = marker.getLatLng().lng;
        marker._target[3] = marker.getLatLng().lat;
        this._update();
        this._reset();
      }, this);

      if (!removable) return;
      marker.on("dblclick", function() {
        this._map.removeLayer(marker);
        var a = this._groundControlPoints.filter(function(b) {
          return b !== marker._target;
        });
        this._groundControlPoints = a;
        this._update();
        this._reset();
      }, this);
    },
    _update: function() {
      this._bounds = L.latLngBounds(this._groundControlPoints.map(function(a) {
        return L.latLng(a[3], a[2]);
      }));
      this._tin = (new Delaunator(this._groundControlPoints.map(function(a) {
        return [a[2], a[3]];
      }))).triangles;
    },
    _reset: function() {

      if (!this._ready) return;

      var min = this._map.latLngToLayerPoint(this._bounds.getNorthWest());
      var max = this._map.latLngToLayerPoint(this._bounds.getSouthEast());
      var w = max.x - min.x;
      var h = max.y - min.y;

      var vertices = this._groundControlPoints.map(function(a) {
        var p = this._map.latLngToLayerPoint(L.latLng(a[3], a[2]));
        return L.point((p.x - min.x) / w * 2 - 1, (max.y - p.y) / h * 2 - 1);
      }, this);

      var textureCoords = [];
      var vertexCoords = [];
      this._tin.forEach(function(a) {
        var b = this._groundControlPoints[a];
        textureCoords.push(b[0], b[1]);
        var c = vertices[a];
        vertexCoords.push(c.x, c.y);
      }, this);


      var canvas = this._image;
      L.DomUtil.setPosition(canvas, min);
      canvas.style.width = w + 'px';
      canvas.style.height = h + 'px';
      canvas.width = w;
      canvas.height = h;

      var gl = this._gl;
      var pg = this._pg;

      gl.viewport(0, 0, w, h);

      var texture = gl.createTexture();
      gl.bindTexture(gl.TEXTURE_2D, texture);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
      gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
      gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, this._img);

      var xyLocation = gl.getAttribLocation(pg, "xy");
      var xyBuffer = gl.createBuffer();
      gl.bindBuffer(gl.ARRAY_BUFFER, xyBuffer);
      gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(vertexCoords), gl.STATIC_DRAW);
      gl.enableVertexAttribArray(xyLocation);
      gl.bindBuffer(gl.ARRAY_BUFFER, xyBuffer);
      gl.vertexAttribPointer(xyLocation, 2, gl.FLOAT, false, 0, 0);

      var uvBuffer = gl.createBuffer();
      var uvLocation = gl.getAttribLocation(pg, "uv");
      gl.bindBuffer(gl.ARRAY_BUFFER, uvBuffer);
      gl.bufferData(gl.ARRAY_BUFFER, new Float32Array(textureCoords), gl.STATIC_DRAW);
      gl.enableVertexAttribArray(uvLocation);
      gl.bindBuffer(gl.ARRAY_BUFFER, uvBuffer);
      gl.vertexAttribPointer(uvLocation, 2, gl.FLOAT, false, 0, 0);

      gl.drawArrays(gl.TRIANGLES, 0, this._tin.length);

    },
    latLngToTexturePoint: function(latlng) {

      var p0 = [NaN, NaN, latlng.lng, latlng.lat];
      for (var i = 0; i < this._tin.length; i += 3) {
        var p1 = this._groundControlPoints[this._tin[i + 0]];
        var p2 = this._groundControlPoints[this._tin[i + 1]];
        var p3 = this._groundControlPoints[this._tin[i + 2]];
        var v12 = [p2[2] - p1[2], p2[3] - p1[3]];
        var v23 = [p3[2] - p2[2], p3[3] - p2[3]];
        var v31 = [p1[2] - p3[2], p1[3] - p3[3]];
        var v10 = [p0[2] - p1[2], p0[3] - p1[3]];
        var v20 = [p0[2] - p2[2], p0[3] - p2[3]];
        var v30 = [p0[2] - p3[2], p0[3] - p3[3]];
        var c1 = v12[0] * v20[1] - v12[1] * v20[0];
        var c2 = v23[0] * v30[1] - v23[1] * v30[0];
        var c3 = v31[0] * v10[1] - v31[1] * v10[0];
        if ((c1 > 0 && c2 > 0 && c3 > 0) || (c1 < 0 && c2 < 0 && c3 < 0)) {
          var m1 = [p1[2], p1[3], 1, p2[2], p2[3], 1, p3[2], p3[3], 1];
          var m2 = [p1[0], p1[1], 1, p2[0], p2[1], 1, p3[0], p3[1], 1];
          var m3 = [p0[2], p0[3], 1, 0, 0, 0, 0, 0, 0];
          var m4 = multiply(multiply(m2, inverse(m1)), m3);
          return L.point(m4[0], m4[1]);
        }
      }
      return null;
    }
  });
  L.imageOverlay.gl = function(url, groundControlPoints, options) {
    return new L.ImageOverlay.GL(url, groundControlPoints, options);
  };

})();

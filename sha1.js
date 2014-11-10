(function(){

    /**
     * @member SHA1
     * @constructor
     *
		 * Somewhat rewritten by John Paul Barbagallo. Based on Paul Johnston's
		 * work, this library simply provides a SHA1.hex method, which will
		 * consume a given String and return a safe, proper SHA1 hex string.
		 *
     * A JavaScript implementation of the Secure Hash Algorithm, SHA-1, as defined in FIPS 180-1
     * Version 2.2 Copyright Paul Johnston 2000 - 2009.
     * Other contributors: Greg Holt, Andrew Kepert, Ydnar, Lostinet
     * See http://pajhome.org.uk/crypt/md5 for details.
     */
    var SHA1 = function() {

      this.hex = function(s) {
        return rstr2hex(rstr(s));
      };
			
		  function utf8Encode(str) {
		    var x, y, output = '',
		      i = -1,
		      l;

		    if (str && str.length) {
		      l = str.length;
		      while ((i += 1) < l) {
		        /* Decode utf-16 surrogate pairs */
		        x = str.charCodeAt(i);
		        y = i + 1 < l ? str.charCodeAt(i + 1) : 0;
		        if (0xD800 <= x && x <= 0xDBFF && 0xDC00 <= y && y <= 0xDFFF) {
		          x = 0x10000 + ((x & 0x03FF) << 10) + (y & 0x03FF);
		          i += 1;
		        }
		        /* Encode output as utf-8 */
		        if (x <= 0x7F) {
		          output += String.fromCharCode(x);
		        } else if (x <= 0x7FF) {
		          output += String.fromCharCode(0xC0 | ((x >>> 6) & 0x1F),
		            0x80 | (x & 0x3F));
		        } else if (x <= 0xFFFF) {
		          output += String.fromCharCode(0xE0 | ((x >>> 12) & 0x0F),
		            0x80 | ((x >>> 6) & 0x3F),
		            0x80 | (x & 0x3F));
		        } else if (x <= 0x1FFFFF) {
		          output += String.fromCharCode(0xF0 | ((x >>> 18) & 0x07),
		            0x80 | ((x >>> 12) & 0x3F),
		            0x80 | ((x >>> 6) & 0x3F),
		            0x80 | (x & 0x3F));
		        }
		      }
		    }
		    return output;
		  }
			
		  /**
		   * Convert an array of big-endian words to a string
		   */
			
		  function binb2rstr(input) {
		    var i, l = input.length * 32,
		      output = '';
		    for (i = 0; i < l; i += 8) {
		      output += String.fromCharCode((input[i >> 5] >>> (24 - i % 32)) & 0xFF);
		    }
		    return output;
		  }
			
			/**
			 * Convert a raw string to an array of big-endian words
			 * Characters >255 have their high-byte silently ignored.
			 */
			
			function rstr2binb(input) {
			  var i, l = input.length * 8,
			    output = Array(input.length >> 2),
			    lo = output.length;
			  for (i = 0; i < lo; i += 1) {
			    output[i] = 0;
			  }
			  for (i = 0; i < l; i += 8) {
			    output[i >> 5] |= (input.charCodeAt(i / 8) & 0xFF) << (24 - i % 32);
			  }
			  return output;
			}
			
		  /**
		   * Convert a raw string to a hex string
		   */

		  function rstr2hex(input) {
		    var hex_tab = '0123456789abcdef',
		      output = '',
		      x, i = 0,
		      l = input.length;
		    for (; i < l; i += 1) {
		      x = input.charCodeAt(i);
		      output += hex_tab.charAt((x >>> 4) & 0x0F) + hex_tab.charAt(x & 0x0F);
		    }
		    return output;
		  }
			
			/**
			 * Add integers, wrapping at 2^32. This uses 16-bit operations internally
			 * to work around bugs in some JS interpreters.
			 */

			function safe_add(x, y) {
			  var lsw = (x & 0xFFFF) + (y & 0xFFFF),
			    msw = (x >> 16) + (y >> 16) + (lsw >> 16);
			  return (msw << 16) | (lsw & 0xFFFF);
			}
			
			/**
			 * Bitwise rotate a 32-bit number to the left.
			 */

			function bit_rol(num, cnt) {
			  return (num << cnt) | (num >>> (32 - cnt));
			}

      /**
       * Calculate the SHA-512 of a raw string
       */

      function rstr(s) {
        s = utf8Encode(s);
        return binb2rstr(binb(rstr2binb(s), s.length * 8));
      }
			
      /**
       * Calculate the SHA-1 of an array of big-endian words, and a bit length
       */

      function binb(x, len) {
        var i, j, t, olda, oldb, oldc, oldd, olde,
          w = Array(80),
          a = 1732584193,
          b = -271733879,
          c = -1732584194,
          d = 271733878,
          e = -1009589776;

        /* append padding */
        x[len >> 5] |= 0x80 << (24 - len % 32);
        x[((len + 64 >> 9) << 4) + 15] = len;

        for (i = 0; i < x.length; i += 16) {
          olda = a,
          oldb = b;
          oldc = c;
          oldd = d;
          olde = e;

          for (j = 0; j < 80; j += 1) {
            if (j < 16) {
              w[j] = x[i + j];
            } else {
              w[j] = bit_rol(w[j - 3] ^ w[j - 8] ^ w[j - 14] ^ w[j - 16], 1);
            }
            t = safe_add(safe_add(bit_rol(a, 5), sha1_ft(j, b, c, d)),
              safe_add(safe_add(e, w[j]), sha1_kt(j)));
            e = d;
            d = c;
            c = bit_rol(b, 30);
            b = a;
            a = t;
          }

          a = safe_add(a, olda);
          b = safe_add(b, oldb);
          c = safe_add(c, oldc);
          d = safe_add(d, oldd);
          e = safe_add(e, olde);
        }
        return Array(a, b, c, d, e);
      }

      /**
       * Perform the appropriate triplet combination function for the current
       * iteration
       */

      function sha1_ft(t, b, c, d) {
        if (t < 20) {
          return (b & c) | ((~b) & d);
        }
        if (t < 40) {
          return b ^ c ^ d;
        }
        if (t < 60) {
          return (b & c) | (b & d) | (c & d);
        }
        return b ^ c ^ d;
      }

      /**
       * Determine the appropriate additive constant for the current iteration
       */

      function sha1_kt(t) {
        return (t < 20) ? 1518500249 : (t < 40) ? 1859775393 :
          (t < 60) ? -1894007588 : -899497514;
      }
    };
		
		window.SHA1 = new SHA1();
	
})();
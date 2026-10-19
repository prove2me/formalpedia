-- Prove2me | Definitions.Def_dusart_theta_mesh_compact_interval02
-- name    : dusart_theta_mesh_compact_interval02
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T02:58:02.814219+00:00
-- url     : https://prove2.me/theorems/ccb579ff-6ea2-4690-ae12-576cff97227e
-- title:
--   Certified theta upper interval from 1609949440 to 3220562176
-- statement:
--   Put $a=1609949440$, $b=3220562176$, $u=1609919129810472$, and $v=3220498643003530$. The Chebyshev theta function satisfies
--
--   $$10^6\theta(a)\le u\ \Longrightarrow\ \left(10^6\theta(b)\le v\quad\text{and}\quad\forall x\in[a,b),\ \theta(x)\le x+100000+x/10000\right).$$
--
--   This certifies one contiguous interval of the upper bound used in the finite fourth-power logarithmic theta estimate. The endpoint carry can be passed to the next interval.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Complete finite interval certificate.

import Definitions.Def_dusart_theta_mesh_compact_soundness
import Theorems.Thm_dusart_theta_mesh_generic_span_024
import Theorems.Thm_dusart_theta_mesh_generic_group200
import Theorems.Thm_dusart_theta_mesh_generic_group201
import Theorems.Thm_dusart_theta_mesh_generic_group202
import Theorems.Thm_dusart_theta_mesh_generic_group203
import Theorems.Thm_dusart_theta_mesh_generic_group204
import Theorems.Thm_dusart_theta_mesh_generic_group205
import Theorems.Thm_dusart_theta_mesh_generic_group206
import Theorems.Thm_dusart_theta_mesh_generic_group207
import Theorems.Thm_dusart_theta_mesh_generic_group208
import Theorems.Thm_dusart_theta_mesh_generic_group209
import Theorems.Thm_dusart_theta_mesh_generic_group210
import Theorems.Thm_dusart_theta_mesh_generic_group211
import Theorems.Thm_dusart_theta_mesh_generic_group212
import Theorems.Thm_dusart_theta_mesh_generic_group213
import Theorems.Thm_dusart_theta_mesh_generic_group214
import Theorems.Thm_dusart_theta_mesh_generic_group215
import Theorems.Thm_dusart_theta_mesh_generic_group216
import Theorems.Thm_dusart_theta_mesh_generic_group217
import Theorems.Thm_dusart_theta_mesh_generic_group218
import Theorems.Thm_dusart_theta_mesh_generic_group219
import Theorems.Thm_dusart_theta_mesh_generic_group220
import Theorems.Thm_dusart_theta_mesh_generic_group221
import Theorems.Thm_dusart_theta_mesh_generic_group222
import Theorems.Thm_dusart_theta_mesh_generic_group223
import Theorems.Thm_dusart_theta_mesh_generic_group224
import Theorems.Thm_dusart_theta_mesh_generic_group225
import Theorems.Thm_dusart_theta_mesh_generic_group226
import Theorems.Thm_dusart_theta_mesh_generic_group227
import Theorems.Thm_dusart_theta_mesh_generic_group228
import Theorems.Thm_dusart_theta_mesh_generic_group229
import Theorems.Thm_dusart_theta_mesh_generic_group230
import Theorems.Thm_dusart_theta_mesh_generic_group231
import Theorems.Thm_dusart_theta_mesh_generic_group232
import Theorems.Thm_dusart_theta_mesh_generic_group233
import Theorems.Thm_dusart_theta_mesh_generic_group234
import Theorems.Thm_dusart_theta_mesh_generic_group235
import Theorems.Thm_dusart_theta_mesh_generic_group236
import Theorems.Thm_dusart_theta_mesh_generic_group237
import Theorems.Thm_dusart_theta_mesh_generic_group238
import Theorems.Thm_dusart_theta_mesh_generic_group239
import Theorems.Thm_dusart_theta_mesh_generic_group240
import Theorems.Thm_dusart_theta_mesh_generic_group241
import Theorems.Thm_dusart_theta_mesh_generic_group242
import Theorems.Thm_dusart_theta_mesh_generic_group243
import Theorems.Thm_dusart_theta_mesh_generic_group244
import Theorems.Thm_dusart_theta_mesh_generic_group245
import Theorems.Thm_dusart_theta_mesh_generic_group246
import Theorems.Thm_dusart_theta_mesh_generic_group247
import Theorems.Thm_dusart_theta_mesh_generic_group248
import Theorems.Thm_dusart_theta_mesh_generic_group249
import Theorems.Thm_dusart_theta_mesh_generic_group250
import Theorems.Thm_dusart_theta_mesh_generic_group251
import Theorems.Thm_dusart_theta_mesh_generic_group252
import Theorems.Thm_dusart_theta_mesh_generic_group253
import Theorems.Thm_dusart_theta_mesh_generic_group254
import Theorems.Thm_dusart_theta_mesh_generic_group255
import Theorems.Thm_dusart_theta_mesh_generic_group256
import Theorems.Thm_dusart_theta_mesh_generic_group257
import Theorems.Thm_dusart_theta_mesh_generic_group258
import Theorems.Thm_dusart_theta_mesh_generic_group259
import Theorems.Thm_dusart_theta_mesh_generic_group260
import Theorems.Thm_dusart_theta_mesh_generic_group261
import Theorems.Thm_dusart_theta_mesh_generic_group262
import Theorems.Thm_dusart_theta_mesh_generic_group263
import Theorems.Thm_dusart_theta_mesh_generic_group264
import Theorems.Thm_dusart_theta_mesh_generic_group265
import Theorems.Thm_dusart_theta_mesh_generic_group266
import Theorems.Thm_dusart_theta_mesh_generic_group267
import Theorems.Thm_dusart_theta_mesh_generic_group268
import Theorems.Thm_dusart_theta_mesh_generic_group269
import Theorems.Thm_dusart_theta_mesh_generic_group270
import Theorems.Thm_dusart_theta_mesh_generic_group271
import Theorems.Thm_dusart_theta_mesh_generic_group272
import Theorems.Thm_dusart_theta_mesh_generic_group273
import Theorems.Thm_dusart_theta_mesh_generic_group274
import Theorems.Thm_dusart_theta_mesh_generic_group275
import Theorems.Thm_dusart_theta_mesh_generic_group276
import Theorems.Thm_dusart_theta_mesh_generic_group277
import Theorems.Thm_dusart_theta_mesh_generic_group278
import Theorems.Thm_dusart_theta_mesh_generic_group279
import Theorems.Thm_dusart_theta_mesh_generic_group280
import Theorems.Thm_dusart_theta_mesh_generic_group281
import Theorems.Thm_dusart_theta_mesh_generic_group282
import Theorems.Thm_dusart_theta_mesh_generic_group283
import Theorems.Thm_dusart_theta_mesh_generic_group284
import Theorems.Thm_dusart_theta_mesh_generic_group285
import Theorems.Thm_dusart_theta_mesh_generic_group286
import Theorems.Thm_dusart_theta_mesh_generic_group287
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartCompactIntervals
theorem interval2_generic : DusartNumeric.GenericSpec 1609949440 3220562176 1609919129810472 3220498643003530 := by
 intro S step compose
 exact (compose (compose (compose (compose (compose (compose (dusart_theta_mesh_generic_span_024 S step @compose) (dusart_theta_mesh_generic_group200 S step @compose)) (compose (dusart_theta_mesh_generic_group201 S step @compose) (compose (dusart_theta_mesh_generic_group202 S step @compose) (dusart_theta_mesh_generic_group203 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group204 S step @compose) (compose (dusart_theta_mesh_generic_group205 S step @compose) (dusart_theta_mesh_generic_group206 S step @compose))) (compose (dusart_theta_mesh_generic_group207 S step @compose) (compose (dusart_theta_mesh_generic_group208 S step @compose) (dusart_theta_mesh_generic_group209 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group210 S step @compose) (dusart_theta_mesh_generic_group211 S step @compose)) (compose (dusart_theta_mesh_generic_group212 S step @compose) (compose (dusart_theta_mesh_generic_group213 S step @compose) (dusart_theta_mesh_generic_group214 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group215 S step @compose) (compose (dusart_theta_mesh_generic_group216 S step @compose) (dusart_theta_mesh_generic_group217 S step @compose))) (compose (dusart_theta_mesh_generic_group218 S step @compose) (compose (dusart_theta_mesh_generic_group219 S step @compose) (dusart_theta_mesh_generic_group220 S step @compose)))))) (compose (compose (compose (compose (dusart_theta_mesh_generic_group221 S step @compose) (dusart_theta_mesh_generic_group222 S step @compose)) (compose (dusart_theta_mesh_generic_group223 S step @compose) (compose (dusart_theta_mesh_generic_group224 S step @compose) (dusart_theta_mesh_generic_group225 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group226 S step @compose) (compose (dusart_theta_mesh_generic_group227 S step @compose) (dusart_theta_mesh_generic_group228 S step @compose))) (compose (dusart_theta_mesh_generic_group229 S step @compose) (compose (dusart_theta_mesh_generic_group230 S step @compose) (dusart_theta_mesh_generic_group231 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group232 S step @compose) (dusart_theta_mesh_generic_group233 S step @compose)) (compose (dusart_theta_mesh_generic_group234 S step @compose) (compose (dusart_theta_mesh_generic_group235 S step @compose) (dusart_theta_mesh_generic_group236 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group237 S step @compose) (compose (dusart_theta_mesh_generic_group238 S step @compose) (dusart_theta_mesh_generic_group239 S step @compose))) (compose (dusart_theta_mesh_generic_group240 S step @compose) (compose (dusart_theta_mesh_generic_group241 S step @compose) (dusart_theta_mesh_generic_group242 S step @compose))))))) (compose (compose (compose (compose (compose (dusart_theta_mesh_generic_group243 S step @compose) (dusart_theta_mesh_generic_group244 S step @compose)) (compose (dusart_theta_mesh_generic_group245 S step @compose) (compose (dusart_theta_mesh_generic_group246 S step @compose) (dusart_theta_mesh_generic_group247 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group248 S step @compose) (compose (dusart_theta_mesh_generic_group249 S step @compose) (dusart_theta_mesh_generic_group250 S step @compose))) (compose (dusart_theta_mesh_generic_group251 S step @compose) (compose (dusart_theta_mesh_generic_group252 S step @compose) (dusart_theta_mesh_generic_group253 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group254 S step @compose) (dusart_theta_mesh_generic_group255 S step @compose)) (compose (dusart_theta_mesh_generic_group256 S step @compose) (compose (dusart_theta_mesh_generic_group257 S step @compose) (dusart_theta_mesh_generic_group258 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group259 S step @compose) (compose (dusart_theta_mesh_generic_group260 S step @compose) (dusart_theta_mesh_generic_group261 S step @compose))) (compose (dusart_theta_mesh_generic_group262 S step @compose) (compose (dusart_theta_mesh_generic_group263 S step @compose) (dusart_theta_mesh_generic_group264 S step @compose)))))) (compose (compose (compose (compose (dusart_theta_mesh_generic_group265 S step @compose) (dusart_theta_mesh_generic_group266 S step @compose)) (compose (dusart_theta_mesh_generic_group267 S step @compose) (compose (dusart_theta_mesh_generic_group268 S step @compose) (dusart_theta_mesh_generic_group269 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group270 S step @compose) (compose (dusart_theta_mesh_generic_group271 S step @compose) (dusart_theta_mesh_generic_group272 S step @compose))) (compose (dusart_theta_mesh_generic_group273 S step @compose) (compose (dusart_theta_mesh_generic_group274 S step @compose) (dusart_theta_mesh_generic_group275 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group276 S step @compose) (compose (dusart_theta_mesh_generic_group277 S step @compose) (dusart_theta_mesh_generic_group278 S step @compose))) (compose (dusart_theta_mesh_generic_group279 S step @compose) (compose (dusart_theta_mesh_generic_group280 S step @compose) (dusart_theta_mesh_generic_group281 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group282 S step @compose) (compose (dusart_theta_mesh_generic_group283 S step @compose) (dusart_theta_mesh_generic_group284 S step @compose))) (compose (dusart_theta_mesh_generic_group285 S step @compose) (compose (dusart_theta_mesh_generic_group286 S step @compose) (dusart_theta_mesh_generic_group287 S step @compose))))))))
theorem interval2 : DusartMeshUpper.Literal.Spec 1609949440 3220562176 1609919129810472 3220498643003530 :=
 DusartProvedBridge.interpret interval2_generic
end DusartCompactIntervals



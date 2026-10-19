-- Prove2me | Definitions.Def_dusart_theta_mesh_compact_interval03
-- name    : dusart_theta_mesh_compact_interval03
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T02:58:19.285995+00:00
-- url     : https://prove2.me/theorems/1d1ade4b-1ec7-4c76-a47a-63b55fcec41c
-- title:
--   Certified theta upper interval from 3220562176 to 4831174912
-- statement:
--   Put $a=3220562176$, $b=4831174912$, $u=3220498643003530$, and $v=4831110639262732$. The Chebyshev theta function satisfies
--
--   $$10^6\theta(a)\le u\ \Longrightarrow\ \left(10^6\theta(b)\le v\quad\text{and}\quad\forall x\in[a,b),\ \theta(x)\le x+100000+x/10000\right).$$
--
--   This certifies one contiguous interval of the upper bound used in the finite fourth-power logarithmic theta estimate. The endpoint carry can be passed to the next interval.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Complete finite interval certificate.

import Definitions.Def_dusart_theta_mesh_compact_soundness
import Theorems.Thm_dusart_theta_mesh_generic_group288
import Theorems.Thm_dusart_theta_mesh_generic_group289
import Theorems.Thm_dusart_theta_mesh_generic_group290
import Theorems.Thm_dusart_theta_mesh_generic_group291
import Theorems.Thm_dusart_theta_mesh_generic_group292
import Theorems.Thm_dusart_theta_mesh_generic_group293
import Theorems.Thm_dusart_theta_mesh_generic_group294
import Theorems.Thm_dusart_theta_mesh_generic_group295
import Theorems.Thm_dusart_theta_mesh_generic_group296
import Theorems.Thm_dusart_theta_mesh_generic_group297
import Theorems.Thm_dusart_theta_mesh_generic_group298
import Theorems.Thm_dusart_theta_mesh_generic_group299
import Theorems.Thm_dusart_theta_mesh_generic_group300
import Theorems.Thm_dusart_theta_mesh_generic_group301
import Theorems.Thm_dusart_theta_mesh_generic_group302
import Theorems.Thm_dusart_theta_mesh_generic_group303
import Theorems.Thm_dusart_theta_mesh_generic_group304
import Theorems.Thm_dusart_theta_mesh_generic_group305
import Theorems.Thm_dusart_theta_mesh_generic_group306
import Theorems.Thm_dusart_theta_mesh_generic_group307
import Theorems.Thm_dusart_theta_mesh_generic_group308
import Theorems.Thm_dusart_theta_mesh_generic_group309
import Theorems.Thm_dusart_theta_mesh_generic_group310
import Theorems.Thm_dusart_theta_mesh_generic_group311
import Theorems.Thm_dusart_theta_mesh_generic_group312
import Theorems.Thm_dusart_theta_mesh_generic_group313
import Theorems.Thm_dusart_theta_mesh_generic_group314
import Theorems.Thm_dusart_theta_mesh_generic_group315
import Theorems.Thm_dusart_theta_mesh_generic_group316
import Theorems.Thm_dusart_theta_mesh_generic_group317
import Theorems.Thm_dusart_theta_mesh_generic_group318
import Theorems.Thm_dusart_theta_mesh_generic_group319
import Theorems.Thm_dusart_theta_mesh_generic_group320
import Theorems.Thm_dusart_theta_mesh_generic_group321
import Theorems.Thm_dusart_theta_mesh_generic_group322
import Theorems.Thm_dusart_theta_mesh_generic_group323
import Theorems.Thm_dusart_theta_mesh_generic_group324
import Theorems.Thm_dusart_theta_mesh_generic_group325
import Theorems.Thm_dusart_theta_mesh_generic_group326
import Theorems.Thm_dusart_theta_mesh_generic_group327
import Theorems.Thm_dusart_theta_mesh_generic_group328
import Theorems.Thm_dusart_theta_mesh_generic_group329
import Theorems.Thm_dusart_theta_mesh_generic_group330
import Theorems.Thm_dusart_theta_mesh_generic_group331
import Theorems.Thm_dusart_theta_mesh_generic_group332
import Theorems.Thm_dusart_theta_mesh_generic_group333
import Theorems.Thm_dusart_theta_mesh_generic_group334
import Theorems.Thm_dusart_theta_mesh_generic_group335
import Theorems.Thm_dusart_theta_mesh_generic_group336
import Theorems.Thm_dusart_theta_mesh_generic_group337
import Theorems.Thm_dusart_theta_mesh_generic_group338
import Theorems.Thm_dusart_theta_mesh_generic_group339
import Theorems.Thm_dusart_theta_mesh_generic_group340
import Theorems.Thm_dusart_theta_mesh_generic_group341
import Theorems.Thm_dusart_theta_mesh_generic_group342
import Theorems.Thm_dusart_theta_mesh_generic_group343
import Theorems.Thm_dusart_theta_mesh_generic_group344
import Theorems.Thm_dusart_theta_mesh_generic_group345
import Theorems.Thm_dusart_theta_mesh_generic_group346
import Theorems.Thm_dusart_theta_mesh_generic_group347
import Theorems.Thm_dusart_theta_mesh_generic_group348
import Theorems.Thm_dusart_theta_mesh_generic_group349
import Theorems.Thm_dusart_theta_mesh_generic_group350
import Theorems.Thm_dusart_theta_mesh_generic_group351
import Theorems.Thm_dusart_theta_mesh_generic_group352
import Theorems.Thm_dusart_theta_mesh_generic_group353
import Theorems.Thm_dusart_theta_mesh_generic_group354
import Theorems.Thm_dusart_theta_mesh_generic_group355
import Theorems.Thm_dusart_theta_mesh_generic_group356
import Theorems.Thm_dusart_theta_mesh_generic_group357
import Theorems.Thm_dusart_theta_mesh_generic_group358
import Theorems.Thm_dusart_theta_mesh_generic_group359
import Theorems.Thm_dusart_theta_mesh_generic_group360
import Theorems.Thm_dusart_theta_mesh_generic_group361
import Theorems.Thm_dusart_theta_mesh_generic_group362
import Theorems.Thm_dusart_theta_mesh_generic_group363
import Theorems.Thm_dusart_theta_mesh_generic_group364
import Theorems.Thm_dusart_theta_mesh_generic_group365
import Theorems.Thm_dusart_theta_mesh_generic_group366
import Theorems.Thm_dusart_theta_mesh_generic_group367
import Theorems.Thm_dusart_theta_mesh_generic_group368
import Theorems.Thm_dusart_theta_mesh_generic_group369
import Theorems.Thm_dusart_theta_mesh_generic_group370
import Theorems.Thm_dusart_theta_mesh_generic_group371
import Theorems.Thm_dusart_theta_mesh_generic_group372
import Theorems.Thm_dusart_theta_mesh_generic_group373
import Theorems.Thm_dusart_theta_mesh_generic_group374
import Theorems.Thm_dusart_theta_mesh_generic_group375
import Theorems.Thm_dusart_theta_mesh_generic_group376
import Theorems.Thm_dusart_theta_mesh_generic_group377
import Theorems.Thm_dusart_theta_mesh_generic_group378
import Theorems.Thm_dusart_theta_mesh_generic_group379
import Theorems.Thm_dusart_theta_mesh_generic_group380
import Theorems.Thm_dusart_theta_mesh_generic_group381
import Theorems.Thm_dusart_theta_mesh_generic_group382
import Theorems.Thm_dusart_theta_mesh_generic_group383
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartCompactIntervals
theorem interval3_generic : DusartNumeric.GenericSpec 3220562176 4831174912 3220498643003530 4831110639262732 := by
 intro S step compose
 exact (compose (compose (compose (compose (compose (compose (dusart_theta_mesh_generic_group288 S step @compose) (compose (dusart_theta_mesh_generic_group289 S step @compose) (dusart_theta_mesh_generic_group290 S step @compose))) (compose (dusart_theta_mesh_generic_group291 S step @compose) (compose (dusart_theta_mesh_generic_group292 S step @compose) (dusart_theta_mesh_generic_group293 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group294 S step @compose) (compose (dusart_theta_mesh_generic_group295 S step @compose) (dusart_theta_mesh_generic_group296 S step @compose))) (compose (dusart_theta_mesh_generic_group297 S step @compose) (compose (dusart_theta_mesh_generic_group298 S step @compose) (dusart_theta_mesh_generic_group299 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group300 S step @compose) (compose (dusart_theta_mesh_generic_group301 S step @compose) (dusart_theta_mesh_generic_group302 S step @compose))) (compose (dusart_theta_mesh_generic_group303 S step @compose) (compose (dusart_theta_mesh_generic_group304 S step @compose) (dusart_theta_mesh_generic_group305 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group306 S step @compose) (compose (dusart_theta_mesh_generic_group307 S step @compose) (dusart_theta_mesh_generic_group308 S step @compose))) (compose (dusart_theta_mesh_generic_group309 S step @compose) (compose (dusart_theta_mesh_generic_group310 S step @compose) (dusart_theta_mesh_generic_group311 S step @compose)))))) (compose (compose (compose (compose (dusart_theta_mesh_generic_group312 S step @compose) (compose (dusart_theta_mesh_generic_group313 S step @compose) (dusart_theta_mesh_generic_group314 S step @compose))) (compose (dusart_theta_mesh_generic_group315 S step @compose) (compose (dusart_theta_mesh_generic_group316 S step @compose) (dusart_theta_mesh_generic_group317 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group318 S step @compose) (compose (dusart_theta_mesh_generic_group319 S step @compose) (dusart_theta_mesh_generic_group320 S step @compose))) (compose (dusart_theta_mesh_generic_group321 S step @compose) (compose (dusart_theta_mesh_generic_group322 S step @compose) (dusart_theta_mesh_generic_group323 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group324 S step @compose) (compose (dusart_theta_mesh_generic_group325 S step @compose) (dusart_theta_mesh_generic_group326 S step @compose))) (compose (dusart_theta_mesh_generic_group327 S step @compose) (compose (dusart_theta_mesh_generic_group328 S step @compose) (dusart_theta_mesh_generic_group329 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group330 S step @compose) (compose (dusart_theta_mesh_generic_group331 S step @compose) (dusart_theta_mesh_generic_group332 S step @compose))) (compose (dusart_theta_mesh_generic_group333 S step @compose) (compose (dusart_theta_mesh_generic_group334 S step @compose) (dusart_theta_mesh_generic_group335 S step @compose))))))) (compose (compose (compose (compose (compose (dusart_theta_mesh_generic_group336 S step @compose) (compose (dusart_theta_mesh_generic_group337 S step @compose) (dusart_theta_mesh_generic_group338 S step @compose))) (compose (dusart_theta_mesh_generic_group339 S step @compose) (compose (dusart_theta_mesh_generic_group340 S step @compose) (dusart_theta_mesh_generic_group341 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group342 S step @compose) (compose (dusart_theta_mesh_generic_group343 S step @compose) (dusart_theta_mesh_generic_group344 S step @compose))) (compose (dusart_theta_mesh_generic_group345 S step @compose) (compose (dusart_theta_mesh_generic_group346 S step @compose) (dusart_theta_mesh_generic_group347 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group348 S step @compose) (compose (dusart_theta_mesh_generic_group349 S step @compose) (dusart_theta_mesh_generic_group350 S step @compose))) (compose (dusart_theta_mesh_generic_group351 S step @compose) (compose (dusart_theta_mesh_generic_group352 S step @compose) (dusart_theta_mesh_generic_group353 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group354 S step @compose) (compose (dusart_theta_mesh_generic_group355 S step @compose) (dusart_theta_mesh_generic_group356 S step @compose))) (compose (dusart_theta_mesh_generic_group357 S step @compose) (compose (dusart_theta_mesh_generic_group358 S step @compose) (dusart_theta_mesh_generic_group359 S step @compose)))))) (compose (compose (compose (compose (dusart_theta_mesh_generic_group360 S step @compose) (compose (dusart_theta_mesh_generic_group361 S step @compose) (dusart_theta_mesh_generic_group362 S step @compose))) (compose (dusart_theta_mesh_generic_group363 S step @compose) (compose (dusart_theta_mesh_generic_group364 S step @compose) (dusart_theta_mesh_generic_group365 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group366 S step @compose) (compose (dusart_theta_mesh_generic_group367 S step @compose) (dusart_theta_mesh_generic_group368 S step @compose))) (compose (dusart_theta_mesh_generic_group369 S step @compose) (compose (dusart_theta_mesh_generic_group370 S step @compose) (dusart_theta_mesh_generic_group371 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group372 S step @compose) (compose (dusart_theta_mesh_generic_group373 S step @compose) (dusart_theta_mesh_generic_group374 S step @compose))) (compose (dusart_theta_mesh_generic_group375 S step @compose) (compose (dusart_theta_mesh_generic_group376 S step @compose) (dusart_theta_mesh_generic_group377 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group378 S step @compose) (compose (dusart_theta_mesh_generic_group379 S step @compose) (dusart_theta_mesh_generic_group380 S step @compose))) (compose (dusart_theta_mesh_generic_group381 S step @compose) (compose (dusart_theta_mesh_generic_group382 S step @compose) (dusart_theta_mesh_generic_group383 S step @compose))))))))
theorem interval3 : DusartMeshUpper.Literal.Spec 3220562176 4831174912 3220498643003530 4831110639262732 :=
 DusartProvedBridge.interpret interval3_generic
end DusartCompactIntervals



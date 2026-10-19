-- Prove2me | Definitions.Def_dusart_theta_mesh_compact_interval04
-- name    : dusart_theta_mesh_compact_interval04
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-17T02:59:04.764734+00:00
-- url     : https://prove2.me/theorems/a74359ae-8d96-4bcd-bf8f-86c651de5e10
-- title:
--   Certified theta upper interval from 4831174912 to 6441787648
-- statement:
--   Put $a=4831174912$, $b=6441787648$, $u=4831110639262732$, and $v=6441698088936622$. The Chebyshev theta function satisfies
--
--   $$10^6\theta(a)\le u\ \Longrightarrow\ \left(10^6\theta(b)\le v\quad\text{and}\quad\forall x\in[a,b),\ \theta(x)\le x+100000+x/10000\right).$$
--
--   This certifies one contiguous interval of the upper bound used in the finite fourth-power logarithmic theta estimate. The endpoint carry can be passed to the next interval.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J.45 (2018),227-251, Theorem 4.2, pp.234-237; DOI 10.1007/s11139-016-9839-4. Complete finite interval certificate.

import Definitions.Def_dusart_theta_mesh_compact_soundness
import Theorems.Thm_dusart_theta_mesh_generic_group384
import Theorems.Thm_dusart_theta_mesh_generic_group385
import Theorems.Thm_dusart_theta_mesh_generic_group386
import Theorems.Thm_dusart_theta_mesh_generic_group387
import Theorems.Thm_dusart_theta_mesh_generic_group388
import Theorems.Thm_dusart_theta_mesh_generic_group389
import Theorems.Thm_dusart_theta_mesh_generic_group390
import Theorems.Thm_dusart_theta_mesh_generic_group391
import Theorems.Thm_dusart_theta_mesh_generic_group392
import Theorems.Thm_dusart_theta_mesh_generic_group393
import Theorems.Thm_dusart_theta_mesh_generic_group394
import Theorems.Thm_dusart_theta_mesh_generic_group395
import Theorems.Thm_dusart_theta_mesh_generic_group396
import Theorems.Thm_dusart_theta_mesh_generic_group397
import Theorems.Thm_dusart_theta_mesh_generic_group398
import Theorems.Thm_dusart_theta_mesh_generic_group399
import Theorems.Thm_dusart_theta_mesh_generic_group400
import Theorems.Thm_dusart_theta_mesh_generic_group401
import Theorems.Thm_dusart_theta_mesh_generic_group402
import Theorems.Thm_dusart_theta_mesh_generic_group403
import Theorems.Thm_dusart_theta_mesh_generic_group404
import Theorems.Thm_dusart_theta_mesh_generic_group405
import Theorems.Thm_dusart_theta_mesh_generic_group406
import Theorems.Thm_dusart_theta_mesh_generic_group407
import Theorems.Thm_dusart_theta_mesh_generic_group408
import Theorems.Thm_dusart_theta_mesh_generic_group409
import Theorems.Thm_dusart_theta_mesh_generic_group410
import Theorems.Thm_dusart_theta_mesh_generic_group411
import Theorems.Thm_dusart_theta_mesh_generic_group412
import Theorems.Thm_dusart_theta_mesh_generic_group413
import Theorems.Thm_dusart_theta_mesh_generic_group414
import Theorems.Thm_dusart_theta_mesh_generic_group415
import Theorems.Thm_dusart_theta_mesh_generic_group416
import Theorems.Thm_dusart_theta_mesh_generic_group417
import Theorems.Thm_dusart_theta_mesh_generic_group418
import Theorems.Thm_dusart_theta_mesh_generic_group419
import Theorems.Thm_dusart_theta_mesh_generic_group420
import Theorems.Thm_dusart_theta_mesh_generic_group421
import Theorems.Thm_dusart_theta_mesh_generic_group422
import Theorems.Thm_dusart_theta_mesh_generic_group423
import Theorems.Thm_dusart_theta_mesh_generic_group424
import Theorems.Thm_dusart_theta_mesh_generic_group425
import Theorems.Thm_dusart_theta_mesh_generic_group426
import Theorems.Thm_dusart_theta_mesh_generic_group427
import Theorems.Thm_dusart_theta_mesh_generic_group428
import Theorems.Thm_dusart_theta_mesh_generic_group429
import Theorems.Thm_dusart_theta_mesh_generic_group430
import Theorems.Thm_dusart_theta_mesh_generic_group431
import Theorems.Thm_dusart_theta_mesh_generic_group432
import Theorems.Thm_dusart_theta_mesh_generic_group433
import Theorems.Thm_dusart_theta_mesh_generic_group434
import Theorems.Thm_dusart_theta_mesh_generic_group435
import Theorems.Thm_dusart_theta_mesh_generic_group436
import Theorems.Thm_dusart_theta_mesh_generic_group437
import Theorems.Thm_dusart_theta_mesh_generic_group438
import Theorems.Thm_dusart_theta_mesh_generic_group439
import Theorems.Thm_dusart_theta_mesh_generic_group440
import Theorems.Thm_dusart_theta_mesh_generic_group441
import Theorems.Thm_dusart_theta_mesh_generic_group442
import Theorems.Thm_dusart_theta_mesh_generic_group443
import Theorems.Thm_dusart_theta_mesh_generic_group444
import Theorems.Thm_dusart_theta_mesh_generic_group445
import Theorems.Thm_dusart_theta_mesh_generic_group446
import Theorems.Thm_dusart_theta_mesh_generic_group447
import Theorems.Thm_dusart_theta_mesh_generic_group448
import Theorems.Thm_dusart_theta_mesh_generic_group449
import Theorems.Thm_dusart_theta_mesh_generic_group450
import Theorems.Thm_dusart_theta_mesh_generic_group451
import Theorems.Thm_dusart_theta_mesh_generic_group452
import Theorems.Thm_dusart_theta_mesh_generic_group453
import Theorems.Thm_dusart_theta_mesh_generic_group454
import Theorems.Thm_dusart_theta_mesh_generic_group455
import Theorems.Thm_dusart_theta_mesh_generic_group456
import Theorems.Thm_dusart_theta_mesh_generic_group457
import Theorems.Thm_dusart_theta_mesh_generic_group458
import Theorems.Thm_dusart_theta_mesh_generic_group459
import Theorems.Thm_dusart_theta_mesh_generic_group460
import Theorems.Thm_dusart_theta_mesh_generic_group461
import Theorems.Thm_dusart_theta_mesh_generic_group462
import Theorems.Thm_dusart_theta_mesh_generic_group463
import Theorems.Thm_dusart_theta_mesh_generic_group464
import Theorems.Thm_dusart_theta_mesh_generic_group465
import Theorems.Thm_dusart_theta_mesh_generic_group466
import Theorems.Thm_dusart_theta_mesh_generic_group467
import Theorems.Thm_dusart_theta_mesh_generic_group468
import Theorems.Thm_dusart_theta_mesh_generic_group469
import Theorems.Thm_dusart_theta_mesh_generic_group470
import Theorems.Thm_dusart_theta_mesh_generic_group471
import Theorems.Thm_dusart_theta_mesh_generic_group472
import Theorems.Thm_dusart_theta_mesh_generic_group473
import Theorems.Thm_dusart_theta_mesh_generic_group474
import Theorems.Thm_dusart_theta_mesh_generic_group475
import Theorems.Thm_dusart_theta_mesh_generic_group476
import Theorems.Thm_dusart_theta_mesh_generic_group477
import Theorems.Thm_dusart_theta_mesh_generic_group478
import Theorems.Thm_dusart_theta_mesh_generic_group479
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace DusartCompactIntervals
theorem interval4_generic : DusartNumeric.GenericSpec 4831174912 6441787648 4831110639262732 6441698088936622 := by
 intro S step compose
 exact (compose (compose (compose (compose (compose (compose (dusart_theta_mesh_generic_group384 S step @compose) (compose (dusart_theta_mesh_generic_group385 S step @compose) (dusart_theta_mesh_generic_group386 S step @compose))) (compose (dusart_theta_mesh_generic_group387 S step @compose) (compose (dusart_theta_mesh_generic_group388 S step @compose) (dusart_theta_mesh_generic_group389 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group390 S step @compose) (compose (dusart_theta_mesh_generic_group391 S step @compose) (dusart_theta_mesh_generic_group392 S step @compose))) (compose (dusart_theta_mesh_generic_group393 S step @compose) (compose (dusart_theta_mesh_generic_group394 S step @compose) (dusart_theta_mesh_generic_group395 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group396 S step @compose) (compose (dusart_theta_mesh_generic_group397 S step @compose) (dusart_theta_mesh_generic_group398 S step @compose))) (compose (dusart_theta_mesh_generic_group399 S step @compose) (compose (dusart_theta_mesh_generic_group400 S step @compose) (dusart_theta_mesh_generic_group401 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group402 S step @compose) (compose (dusart_theta_mesh_generic_group403 S step @compose) (dusart_theta_mesh_generic_group404 S step @compose))) (compose (dusart_theta_mesh_generic_group405 S step @compose) (compose (dusart_theta_mesh_generic_group406 S step @compose) (dusart_theta_mesh_generic_group407 S step @compose)))))) (compose (compose (compose (compose (dusart_theta_mesh_generic_group408 S step @compose) (compose (dusart_theta_mesh_generic_group409 S step @compose) (dusart_theta_mesh_generic_group410 S step @compose))) (compose (dusart_theta_mesh_generic_group411 S step @compose) (compose (dusart_theta_mesh_generic_group412 S step @compose) (dusart_theta_mesh_generic_group413 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group414 S step @compose) (compose (dusart_theta_mesh_generic_group415 S step @compose) (dusart_theta_mesh_generic_group416 S step @compose))) (compose (dusart_theta_mesh_generic_group417 S step @compose) (compose (dusart_theta_mesh_generic_group418 S step @compose) (dusart_theta_mesh_generic_group419 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group420 S step @compose) (compose (dusart_theta_mesh_generic_group421 S step @compose) (dusart_theta_mesh_generic_group422 S step @compose))) (compose (dusart_theta_mesh_generic_group423 S step @compose) (compose (dusart_theta_mesh_generic_group424 S step @compose) (dusart_theta_mesh_generic_group425 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group426 S step @compose) (compose (dusart_theta_mesh_generic_group427 S step @compose) (dusart_theta_mesh_generic_group428 S step @compose))) (compose (dusart_theta_mesh_generic_group429 S step @compose) (compose (dusart_theta_mesh_generic_group430 S step @compose) (dusart_theta_mesh_generic_group431 S step @compose))))))) (compose (compose (compose (compose (compose (dusart_theta_mesh_generic_group432 S step @compose) (compose (dusart_theta_mesh_generic_group433 S step @compose) (dusart_theta_mesh_generic_group434 S step @compose))) (compose (dusart_theta_mesh_generic_group435 S step @compose) (compose (dusart_theta_mesh_generic_group436 S step @compose) (dusart_theta_mesh_generic_group437 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group438 S step @compose) (compose (dusart_theta_mesh_generic_group439 S step @compose) (dusart_theta_mesh_generic_group440 S step @compose))) (compose (dusart_theta_mesh_generic_group441 S step @compose) (compose (dusart_theta_mesh_generic_group442 S step @compose) (dusart_theta_mesh_generic_group443 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group444 S step @compose) (compose (dusart_theta_mesh_generic_group445 S step @compose) (dusart_theta_mesh_generic_group446 S step @compose))) (compose (dusart_theta_mesh_generic_group447 S step @compose) (compose (dusart_theta_mesh_generic_group448 S step @compose) (dusart_theta_mesh_generic_group449 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group450 S step @compose) (compose (dusart_theta_mesh_generic_group451 S step @compose) (dusart_theta_mesh_generic_group452 S step @compose))) (compose (dusart_theta_mesh_generic_group453 S step @compose) (compose (dusart_theta_mesh_generic_group454 S step @compose) (dusart_theta_mesh_generic_group455 S step @compose)))))) (compose (compose (compose (compose (dusart_theta_mesh_generic_group456 S step @compose) (compose (dusart_theta_mesh_generic_group457 S step @compose) (dusart_theta_mesh_generic_group458 S step @compose))) (compose (dusart_theta_mesh_generic_group459 S step @compose) (compose (dusart_theta_mesh_generic_group460 S step @compose) (dusart_theta_mesh_generic_group461 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group462 S step @compose) (compose (dusart_theta_mesh_generic_group463 S step @compose) (dusart_theta_mesh_generic_group464 S step @compose))) (compose (dusart_theta_mesh_generic_group465 S step @compose) (compose (dusart_theta_mesh_generic_group466 S step @compose) (dusart_theta_mesh_generic_group467 S step @compose))))) (compose (compose (compose (dusart_theta_mesh_generic_group468 S step @compose) (compose (dusart_theta_mesh_generic_group469 S step @compose) (dusart_theta_mesh_generic_group470 S step @compose))) (compose (dusart_theta_mesh_generic_group471 S step @compose) (compose (dusart_theta_mesh_generic_group472 S step @compose) (dusart_theta_mesh_generic_group473 S step @compose)))) (compose (compose (dusart_theta_mesh_generic_group474 S step @compose) (compose (dusart_theta_mesh_generic_group475 S step @compose) (dusart_theta_mesh_generic_group476 S step @compose))) (compose (dusart_theta_mesh_generic_group477 S step @compose) (compose (dusart_theta_mesh_generic_group478 S step @compose) (dusart_theta_mesh_generic_group479 S step @compose))))))))
theorem interval4 : DusartMeshUpper.Literal.Spec 4831174912 6441787648 4831110639262732 6441698088936622 :=
 DusartProvedBridge.interpret interval4_generic
end DusartCompactIntervals



-- Prove2me | Definitions.Def_HardyCapsetEvaluationData173rows09V420261021
-- name    : HardyCapsetEvaluationData173rows09V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:09:10.744921+00:00
-- url     : https://prove2.me/theorems/59481331-ffa7-4d11-a3f9-b7737b3b8009
-- title:
--   HardyCapsetEvaluationData173rows09V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er173_576 : Row := { vars := #[501, 667, 668], coeff := #[1, 1, 1], bound := 1, weight := 104432, edges := #[⟨0, 1, 157⟩, ⟨0, 2, 155⟩, ⟨1, 2, 480⟩], triples := #[] }
def er173_577 : Row := { vars := #[502, 100, 553], coeff := #[1, 1, 1], bound := 1, weight := 376884, edges := #[⟨0, 1, 437⟩, ⟨0, 2, 97⟩, ⟨1, 2, 197⟩], triples := #[] }
def er173_578 : Row := { vars := #[503, 582, 629, 669], coeff := #[1, 1, 1, 1], bound := 1, weight := 628584, edges := #[⟨0, 1, 24⟩, ⟨0, 2, 59⟩, ⟨0, 3, 157⟩, ⟨1, 2, 426⟩, ⟨1, 3, 400⟩, ⟨2, 3, 369⟩], triples := #[] }
def er173_579 : Row := { vars := #[503, 667, 552, 630], coeff := #[1, 1, 1, 1], bound := 1, weight := 149441, edges := #[⟨0, 1, 156⟩, ⟨0, 2, 97⟩, ⟨0, 3, 60⟩, ⟨1, 2, 426⟩, ⟨1, 3, 371⟩, ⟨2, 3, 464⟩], triples := #[] }
def er173_580 : Row := { vars := #[506, 230, 512], coeff := #[1, 1, 1], bound := 1, weight := 313265, edges := #[⟨0, 1, 487⟩, ⟨0, 2, 349⟩, ⟨1, 2, 483⟩], triples := #[] }
def er173_581 : Row := { vars := #[507, 99, 513], coeff := #[1, 1, 1], bound := 1, weight := 168534, edges := #[⟨0, 1, 455⟩, ⟨0, 2, 350⟩, ⟨1, 2, 451⟩], triples := #[] }
def er173_582 : Row := { vars := #[507, 548, 583], coeff := #[1, 1, 1], bound := 1, weight := 345407, edges := #[⟨0, 1, 91⟩, ⟨0, 2, 7⟩, ⟨1, 2, 506⟩], triples := #[] }
def er173_583 : Row := { vars := #[507, 563, 628], coeff := #[1, 1, 1], bound := 1, weight := 486061, edges := #[⟨0, 1, 126⟩, ⟨0, 2, 43⟩, ⟨1, 2, 506⟩], triples := #[] }
def er173_584 : Row := { vars := #[508, 616, 582], coeff := #[1, 1, 1], bound := 1, weight := 198781, edges := #[⟨0, 1, 54⟩, ⟨0, 2, 6⟩, ⟨1, 2, 431⟩], triples := #[] }
def er173_585 : Row := { vars := #[509, 623, 627, 663], coeff := #[1, 1, 1, 1], bound := 1, weight := 447216, edges := #[⟨0, 1, 48⟩, ⟨0, 2, 40⟩, ⟨0, 3, 139⟩, ⟨1, 2, 447⟩, ⟨1, 3, 369⟩, ⟨2, 3, 365⟩], triples := #[] }
def er173_586 : Row := { vars := #[510, 662, 624, 666], coeff := #[1, 1, 1, 1], bound := 1, weight := 24528, edges := #[⟨0, 1, 142⟩, ⟨0, 2, 42⟩, ⟨0, 3, 134⟩, ⟨1, 2, 371⟩, ⟨1, 3, 479⟩, ⟨2, 3, 367⟩], triples := #[] }
def er173_587 : Row := { vars := #[514, 576, 546], coeff := #[1, 1, 1], bound := 1, weight := 196456, edges := #[⟨0, 1, 24⟩, ⟨0, 2, 97⟩, ⟨1, 2, 492⟩], triples := #[] }
def er173_588 : Row := { vars := #[514, 589, 635], coeff := #[1, 1, 1], bound := 1, weight := 650266, edges := #[⟨0, 1, 29⟩, ⟨0, 2, 65⟩, ⟨1, 2, 434⟩], triples := #[] }
def er173_589 : Row := { vars := #[516, 674, 676, 558], coeff := #[1, 1, 1, 1], bound := 1, weight := 473948, edges := #[⟨0, 1, 166⟩, ⟨0, 2, 167⟩, ⟨0, 3, 107⟩, ⟨1, 2, 487⟩, ⟨1, 3, 433⟩, ⟨2, 3, 435⟩], triples := #[] }
def er173_590 : Row := { vars := #[517, 525, 535], coeff := #[1, 1, 1], bound := 1, weight := 24528, edges := #[⟨0, 1, 375⟩, ⟨0, 2, 360⟩, ⟨1, 2, 355⟩], triples := #[] }
def er173_591 : Row := { vars := #[517, 686, 535], coeff := #[1, 1, 1], bound := 1, weight := 975473, edges := #[⟨0, 1, 427⟩, ⟨0, 2, 360⟩, ⟨1, 2, 416⟩], triples := #[] }
def er173_592 : Row := { vars := #[518, 527, 534], coeff := #[1, 1, 1], bound := 1, weight := 471195, edges := #[⟨0, 1, 373⟩, ⟨0, 2, 360⟩, ⟨1, 2, 352⟩], triples := #[] }
def er173_593 : Row := { vars := #[518, 685, 536], coeff := #[1, 1, 1], bound := 1, weight := 425160, edges := #[⟨0, 1, 427⟩, ⟨0, 2, 361⟩, ⟨1, 2, 416⟩], triples := #[] }
def er173_594 : Row := { vars := #[518, 599, 536], coeff := #[1, 1, 1], bound := 1, weight := 103646, edges := #[⟨0, 1, 503⟩, ⟨0, 2, 361⟩, ⟨1, 2, 492⟩], triples := #[] }
def er173_595 : Row := { vars := #[519, 528, 532], coeff := #[1, 1, 1], bound := 1, weight := 727304, edges := #[⟨0, 1, 374⟩, ⟨0, 2, 360⟩, ⟨1, 2, 352⟩], triples := #[] }
def er173_596 : Row := { vars := #[519, 575, 590], coeff := #[1, 1, 1], bound := 1, weight := 248170, edges := #[⟨0, 1, 458⟩, ⟨0, 2, 491⟩, ⟨1, 2, 438⟩], triples := #[] }
def er173_597 : Row := { vars := #[520, 529, 533], coeff := #[1, 1, 1], bound := 1, weight := 613912, edges := #[⟨0, 1, 375⟩, ⟨0, 2, 361⟩, ⟨1, 2, 353⟩], triples := #[] }
def er173_598 : Row := { vars := #[520, 529, 537], coeff := #[1, 1, 1], bound := 1, weight := 192271, edges := #[⟨0, 1, 375⟩, ⟨0, 2, 362⟩, ⟨1, 2, 354⟩], triples := #[] }
def er173_599 : Row := { vars := #[520, 675, 362], coeff := #[1, 1, 1], bound := 1, weight := 193819, edges := #[⟨0, 1, 444⟩, ⟨0, 2, 160⟩, ⟨1, 2, 43⟩], triples := #[] }
def er173_600 : Row := { vars := #[525, 548, 555], coeff := #[1, 1, 1], bound := 1, weight := 65918, edges := #[⟨0, 1, 401⟩, ⟨0, 2, 396⟩, ⟨1, 2, 388⟩], triples := #[] }
def er173_601 : Row := { vars := #[526, 617, 625], coeff := #[1, 1, 1], bound := 1, weight := 526110, edges := #[⟨0, 1, 487⟩, ⟨0, 2, 477⟩, ⟨1, 2, 451⟩], triples := #[] }
def er173_602 : Row := { vars := #[526, 656, 664], coeff := #[1, 1, 1], bound := 1, weight := 119511, edges := #[⟨0, 1, 455⟩, ⟨0, 2, 445⟩, ⟨1, 2, 483⟩], triples := #[] }
def er173_603 : Row := { vars := #[527, 680, 688], coeff := #[1, 1, 1], bound := 1, weight := 528806, edges := #[⟨0, 1, 434⟩, ⟨0, 2, 424⟩, ⟨1, 2, 505⟩], triples := #[] }
def er173_604 : Row := { vars := #[528, 681, 689], coeff := #[1, 1, 1], bound := 1, weight := 144888, edges := #[⟨0, 1, 435⟩, ⟨0, 2, 425⟩, ⟨1, 2, 506⟩], triples := #[] }
def er173_605 : Row := { vars := #[528, 595, 603], coeff := #[1, 1, 1], bound := 1, weight := 127810, edges := #[⟨0, 1, 510⟩, ⟨0, 2, 500⟩, ⟨1, 2, 431⟩], triples := #[] }
def er173_606 : Row := { vars := #[530, 661, 665], coeff := #[1, 1, 1], bound := 1, weight := 447216, edges := #[⟨0, 1, 448⟩, ⟨0, 2, 444⟩, ⟨1, 2, 478⟩], triples := #[] }
def er173_607 : Row := { vars := #[531, 641, 643], coeff := #[1, 1, 1], bound := 1, weight := 34376, edges := #[⟨0, 1, 408⟩, ⟨0, 2, 406⟩, ⟨1, 2, 465⟩], triples := #[] }
def er173_608 : Row := { vars := #[531, 650, 672], coeff := #[1, 1, 1], bound := 1, weight := 54039, edges := #[⟨0, 1, 413⟩, ⟨0, 2, 456⟩, ⟨1, 2, 506⟩], triples := #[] }
def er173_609 : Row := { vars := #[533, 542, 522], coeff := #[1, 1, 1], bound := 1, weight := 124341, edges := #[⟨0, 1, 381⟩, ⟨0, 2, 369⟩, ⟨1, 2, 365⟩], triples := #[] }
def er173_610 : Row := { vars := #[534, 543, 617], coeff := #[1, 1, 1], bound := 1, weight := 86872, edges := #[⟨0, 1, 382⟩, ⟨0, 2, 480⟩, ⟨1, 2, 476⟩], triples := #[] }
def er173_611 : Row := { vars := #[537, 544, 595], coeff := #[1, 1, 1], bound := 1, weight := 31168, edges := #[⟨0, 1, 383⟩, ⟨0, 2, 502⟩, ⟨1, 2, 498⟩], triples := #[] }
def er173_612 : Row := { vars := #[537, 544, 524], coeff := #[1, 1, 1], bound := 1, weight := 656662, edges := #[⟨0, 1, 383⟩, ⟨0, 2, 371⟩, ⟨1, 2, 367⟩], triples := #[] }
def er173_613 : Row := { vars := #[538, 542, 522], coeff := #[1, 1, 1], bound := 1, weight := 613912, edges := #[⟨0, 1, 382⟩, ⟨0, 2, 370⟩, ⟨1, 2, 365⟩], triples := #[] }
def er173_614 : Row := { vars := #[539, 541, 521], coeff := #[1, 1, 1], bound := 1, weight := 727304, edges := #[⟨0, 1, 382⟩, ⟨0, 2, 370⟩, ⟨1, 2, 364⟩], triples := #[] }
def er173_615 : Row := { vars := #[540, 608, 610], coeff := #[1, 1, 1], bound := 1, weight := 366928, edges := #[⟨0, 1, 511⟩, ⟨0, 2, 507⟩, ⟨1, 2, 432⟩], triples := #[] }
def er173_616 : Row := { vars := #[543, 555, 523], coeff := #[1, 1, 1], bound := 1, weight := 787560, edges := #[⟨0, 1, 403⟩, ⟨0, 2, 366⟩, ⟨1, 2, 400⟩], triples := #[] }
def er173_617 : Row := { vars := #[545, 98, 654, 591], coeff := #[1, 1, 1, 1], bound := 1, weight := 344726, edges := #[⟨0, 1, 210⟩, ⟨0, 2, 416⟩, ⟨0, 3, 470⟩, ⟨1, 2, 250⟩, ⟨1, 3, 304⟩, ⟨2, 3, 386⟩], triples := #[] }
def er173_618 : Row := { vars := #[546, 562, 547, 98], coeff := #[1, 1, 1, 1], bound := 1, weight := 121790, edges := #[⟨0, 1, 355⟩, ⟨0, 2, 386⟩, ⟨0, 3, 209⟩, ⟨1, 2, 354⟩, ⟨1, 3, 240⟩, ⟨2, 3, 208⟩], triples := #[] }
def er173_619 : Row := { vars := #[548, 291, 573], coeff := #[1, 1, 1], bound := 1, weight := 439236, edges := #[⟨0, 1, 64⟩, ⟨0, 2, 365⟩, ⟨1, 2, 7⟩], triples := #[] }
def er173_620 : Row := { vars := #[553, 688, 604], coeff := #[1, 1, 1], bound := 1, weight := 24528, edges := #[⟨0, 1, 408⟩, ⟨0, 2, 480⟩, ⟨1, 2, 363⟩], triples := #[] }
def er173_621 : Row := { vars := #[553, 568, 499], coeff := #[1, 1, 1], bound := 1, weight := 216850, edges := #[⟨0, 1, 369⟩, ⟨0, 2, 91⟩, ⟨1, 2, 126⟩], triples := #[] }
def er173_622 : Row := { vars := #[557, 631, 549], coeff := #[1, 1, 1], bound := 1, weight := 615354, edges := #[⟨0, 1, 467⟩, ⟨0, 2, 389⟩, ⟨1, 2, 464⟩], triples := #[] }
def er173_623 : Row := { vars := #[558, 674, 572], coeff := #[1, 1, 1], bound := 1, weight := 276726, edges := #[⟨0, 1, 433⟩, ⟨0, 2, 373⟩, ⟨1, 2, 411⟩], triples := #[] }
def er173_624 : Row := { vars := #[558, 652, 676, 673], coeff := #[1, 1, 1, 1], bound := 1, weight := 249327, edges := #[⟨0, 1, 456⟩, ⟨0, 2, 435⟩, ⟨0, 3, 427⟩, ⟨1, 2, 510⟩, ⟨1, 3, 503⟩, ⟨2, 3, 481⟩], triples := #[] }
def er173_625 : Row := { vars := #[559, 655, 290], coeff := #[1, 1, 1], bound := 1, weight := 447216, edges := #[⟨0, 1, 422⟩, ⟨0, 2, 43⟩, ⟨1, 2, 130⟩], triples := #[] }
def er173_626 : Row := { vars := #[559, 563, 290], coeff := #[1, 1, 1], bound := 1, weight := 224675, edges := #[⟨0, 1, 364⟩, ⟨0, 2, 43⟩, ⟨1, 2, 29⟩], triples := #[] }
def er173_627 : Row := { vars := #[561, 640, 592], coeff := #[1, 1, 1], bound := 1, weight := 199254, edges := #[⟨0, 1, 416⟩, ⟨0, 2, 459⟩, ⟨1, 2, 395⟩], triples := #[] }
def er173_628 : Row := { vars := #[562, 615, 678, 55], coeff := #[1, 1, 1, 1], bound := 1, weight := 319193, edges := #[⟨0, 1, 492⟩, ⟨0, 2, 438⟩, ⟨0, 3, 211⟩, ⟨1, 2, 396⟩, ⟨1, 3, 304⟩, ⟨2, 3, 250⟩], triples := #[] }
def er173_629 : Row := { vars := #[568, 582, 669, 626], coeff := #[1, 1, 1, 1], bound := 1, weight := 172636, edges := #[⟨0, 1, 480⟩, ⟨0, 2, 410⟩, ⟨0, 3, 494⟩, ⟨1, 2, 400⟩, ⟨1, 3, 418⟩, ⟨2, 3, 362⟩], triples := #[] }
def er173_630 : Row := { vars := #[569, 616, 620], coeff := #[1, 1, 1], bound := 1, weight := 591283, edges := #[⟨0, 1, 494⟩, ⟨0, 2, 492⟩, ⟨1, 2, 449⟩], triples := #[] }
def er173_631 : Row := { vars := #[572, 607, 564], coeff := #[1, 1, 1], bound := 1, weight := 429163, edges := #[⟨0, 1, 467⟩, ⟨0, 2, 399⟩, ⟨1, 2, 464⟩], triples := #[] }
def er173_632 : Row := { vars := #[574, 588, 634, 637], coeff := #[1, 1, 1, 1], bound := 1, weight := 660775, edges := #[⟨0, 1, 488⟩, ⟨0, 2, 503⟩, ⟨0, 3, 509⟩, ⟨1, 2, 427⟩, ⟨1, 3, 434⟩, ⟨2, 3, 449⟩], triples := #[] }
def er173_633 : Row := { vars := #[576, 577, 226, 638], coeff := #[1, 1, 1, 1], bound := 1, weight := 748768, edges := #[⟨0, 1, 406⟩, ⟨0, 2, 211⟩, ⟨0, 3, 355⟩, ⟨1, 2, 210⟩, ⟨1, 3, 353⟩, ⟨2, 3, 304⟩], triples := #[] }
def er173_634 : Row := { vars := #[578, 324, 698], coeff := #[1, 1, 1], bound := 1, weight := 288603, edges := #[⟨0, 1, 190⟩, ⟨0, 2, 389⟩, ⟨1, 2, 77⟩], triples := #[] }
def er173_635 : Row := { vars := #[578, 651, 295], coeff := #[1, 1, 1], bound := 1, weight := 287993, edges := #[⟨0, 1, 367⟩, ⟨0, 2, 160⟩, ⟨1, 2, 77⟩], triples := #[] }
def er173_636 : Row := { vars := #[580, 619, 627], coeff := #[1, 1, 1], bound := 1, weight := 552785, edges := #[⟨0, 1, 434⟩, ⟨0, 2, 424⟩, ⟨1, 2, 453⟩], triples := #[] }
def er173_637 : Row := { vars := #[584, 616, 620], coeff := #[1, 1, 1], bound := 1, weight := 209938, edges := #[⟨0, 1, 418⟩, ⟨0, 2, 416⟩, ⟨1, 2, 449⟩], triples := #[] }
def er173_638 : Row := { vars := #[584, 587, 594], coeff := #[1, 1, 1], bound := 1, weight := 172597, edges := #[⟨0, 1, 413⟩, ⟨0, 2, 448⟩, ⟨1, 2, 444⟩], triples := #[] }
def er173_639 : Row := { vars := #[587, 670, 579], coeff := #[1, 1, 1], bound := 1, weight := 337552, edges := #[⟨0, 1, 403⟩, ⟨0, 2, 409⟩, ⟨1, 2, 400⟩], triples := #[] }
end HardyCapset20261020.Cert



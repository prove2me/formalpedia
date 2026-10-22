-- Prove2me | Definitions.Def_HardyCapsetEvaluationData173rows10V420261021
-- name    : HardyCapsetEvaluationData173rows10V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:09:22.939695+00:00
-- url     : https://prove2.me/theorems/eb5303b6-5287-478c-b75c-3c7eb071f6f0
-- title:
--   HardyCapsetEvaluationData173rows10V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er173_640 : Row := { vars := #[592, 607, 684], coeff := #[1, 1, 1], bound := 1, weight := 189817, edges := #[⟨0, 1, 418⟩, ⟨0, 2, 374⟩, ⟨1, 2, 354⟩], triples := #[] }
def er173_641 : Row := { vars := #[592, 607, 596], coeff := #[1, 1, 1], bound := 1, weight := 16411, edges := #[⟨0, 1, 418⟩, ⟨0, 2, 427⟩, ⟨1, 2, 416⟩], triples := #[] }
def er173_642 : Row := { vars := #[594, 596, 602], coeff := #[1, 1, 1], bound := 1, weight := 782078, edges := #[⟨0, 1, 435⟩, ⟨0, 2, 430⟩, ⟨1, 2, 425⟩], triples := #[] }
def er173_643 : Row := { vars := #[595, 596, 603], coeff := #[1, 1, 1], bound := 1, weight := 201512, edges := #[⟨0, 1, 434⟩, ⟨0, 2, 431⟩, ⟨1, 2, 424⟩], triples := #[] }
def er173_644 : Row := { vars := #[601, 691, 692, 606], coeff := #[1, 1, 1, 1], bound := 1, weight := 174731, edges := #[⟨0, 1, 362⟩, ⟨0, 2, 361⟩, ⟨0, 3, 418⟩, ⟨1, 2, 502⟩, ⟨1, 3, 370⟩, ⟨2, 3, 368⟩], triples := #[] }
def er173_645 : Row := { vars := #[604, 690, 605, 693], coeff := #[1, 1, 1, 1], bound := 1, weight := 975473, edges := #[⟨0, 1, 361⟩, ⟨0, 2, 426⟩, ⟨0, 3, 371⟩, ⟨1, 2, 362⟩, ⟨1, 3, 494⟩, ⟨2, 3, 369⟩], triples := #[] }
def er173_646 : Row := { vars := #[606, 347, 691], coeff := #[1, 1, 1], bound := 1, weight := 40841, edges := #[⟨0, 1, 150⟩, ⟨0, 2, 370⟩, ⟨1, 2, 126⟩], triples := #[] }
def er173_647 : Row := { vars := #[607, 642, 650], coeff := #[1, 1, 1], bound := 1, weight := 71192, edges := #[⟨0, 1, 400⟩, ⟨0, 2, 403⟩, ⟨1, 2, 463⟩], triples := #[] }
def er173_648 : Row := { vars := #[608, 610, 619], coeff := #[1, 1, 1], bound := 1, weight := 166558, edges := #[⟨0, 1, 432⟩, ⟨0, 2, 410⟩, ⟨1, 2, 409⟩], triples := #[] }
def er173_649 : Row := { vars := #[608, 683, 679], coeff := #[1, 1, 1], bound := 1, weight := 192429, edges := #[⟨0, 1, 355⟩, ⟨0, 2, 363⟩, ⟨1, 2, 503⟩], triples := #[] }
def er173_650 : Row := { vars := #[610, 698, 699, 700], coeff := #[1, 1, 1, 1], bound := 1, weight := 466516, edges := #[⟨0, 1, 374⟩, ⟨0, 2, 373⟩, ⟨0, 3, 372⟩, ⟨1, 2, 511⟩, ⟨1, 3, 510⟩, ⟨2, 3, 509⟩], triples := #[] }
def er173_651 : Row := { vars := #[611, 612, 613, 697], coeff := #[1, 1, 1, 1], bound := 1, weight := 650266, edges := #[⟨0, 1, 433⟩, ⟨0, 2, 434⟩, ⟨0, 3, 373⟩, ⟨1, 2, 435⟩, ⟨1, 3, 374⟩, ⟨2, 3, 375⟩], triples := #[] }
def er173_652 : Row := { vars := #[617, 621, 625], coeff := #[1, 1, 1], bound := 1, weight := 387020, edges := #[⟨0, 1, 455⟩, ⟨0, 2, 451⟩, ⟨1, 2, 445⟩], triples := #[] }
def er173_653 : Row := { vars := #[623, 670, 655], coeff := #[1, 1, 1], bound := 1, weight := 552785, edges := #[⟨0, 1, 352⟩, ⟨0, 2, 372⟩, ⟨1, 2, 472⟩], triples := #[] }
def er173_654 : Row := { vars := #[635, 636, 673, 637], coeff := #[1, 1, 1, 1], bound := 1, weight := 339226, edges := #[⟨0, 1, 456⟩, ⟨0, 2, 375⟩, ⟨0, 3, 457⟩, ⟨1, 2, 372⟩, ⟨1, 3, 455⟩, ⟨2, 3, 373⟩], triples := #[] }
def er173_655 : Row := { vars := #[638, 139, 653, 677], coeff := #[1, 1, 1, 1], bound := 1, weight := 217923, edges := #[⟨0, 1, 209⟩, ⟨0, 2, 492⟩, ⟨0, 3, 470⟩, ⟨1, 2, 240⟩, ⟨1, 3, 230⟩, ⟨2, 3, 460⟩], triples := #[] }
def er173_656 : Row := { vars := #[641, 692, 668], coeff := #[1, 1, 1], bound := 1, weight := 45010, edges := #[⟨0, 1, 485⟩, ⟨0, 2, 505⟩, ⟨1, 2, 464⟩], triples := #[] }
def er173_657 : Row := { vars := #[647, 679, 683], coeff := #[1, 1, 1], bound := 1, weight := 125231, edges := #[⟨0, 1, 472⟩, ⟨0, 2, 470⟩, ⟨1, 2, 503⟩], triples := #[] }
def er173_658 : Row := { vars := #[647, 650, 656], coeff := #[1, 1, 1], bound := 1, weight := 241292, edges := #[⟨0, 1, 467⟩, ⟨0, 2, 502⟩, ⟨1, 2, 498⟩], triples := #[] }
def er173_659 : Row := { vars := #[652, 292, 679], coeff := #[1, 1, 1], bound := 1, weight := 219308, edges := #[⟨0, 1, 77⟩, ⟨0, 2, 476⟩, ⟨1, 2, 119⟩], triples := #[] }
def er173_660 : Row := { vars := #[658, 659, 666], coeff := #[1, 1, 1], bound := 1, weight := 627662, edges := #[⟨0, 1, 487⟩, ⟨0, 2, 485⟩, ⟨1, 2, 477⟩], triples := #[] }
def er173_661 : Row := { vars := #[660, 664, 521], coeff := #[1, 1, 1], bound := 1, weight := 272697, edges := #[⟨0, 1, 477⟩, ⟨0, 2, 456⟩, ⟨1, 2, 452⟩], triples := #[] }
def er173_662 : Row := { vars := #[660, 664, 642], coeff := #[1, 1, 1], bound := 1, weight := 607793, edges := #[⟨0, 1, 477⟩, ⟨0, 2, 511⟩, ⟨1, 2, 507⟩], triples := #[] }
def er173_663 : Row := { vars := #[662, 666, 524], coeff := #[1, 1, 1], bound := 1, weight := 343339, edges := #[⟨0, 1, 479⟩, ⟨0, 2, 456⟩, ⟨1, 2, 452⟩], triples := #[] }
def er173_664 : Row := { vars := #[662, 666, 549], coeff := #[1, 1, 1], bound := 1, weight := 4473, edges := #[⟨0, 1, 479⟩, ⟨0, 2, 433⟩, ⟨1, 2, 429⟩], triples := #[] }
def er173_665 : Row := { vars := #[679, 683, 694], coeff := #[1, 1, 1], bound := 1, weight := 1960, edges := #[⟨0, 1, 503⟩, ⟨0, 2, 494⟩, ⟨1, 2, 492⟩], triples := #[] }
def er173_666 : Row := { vars := #[681, 683, 689], coeff := #[1, 1, 1], bound := 1, weight := 680382, edges := #[⟨0, 1, 509⟩, ⟨0, 2, 506⟩, ⟨1, 2, 499⟩], triples := #[] }
def er173_667 : Row := { vars := #[684, 688, 523], coeff := #[1, 1, 1], bound := 1, weight := 169332, edges := #[⟨0, 1, 499⟩, ⟨0, 2, 433⟩, ⟨1, 2, 429⟩], triples := #[] }
def er173_668 : Row := { vars := #[684, 688, 564], coeff := #[1, 1, 1], bound := 1, weight := 277336, edges := #[⟨0, 1, 499⟩, ⟨0, 2, 456⟩, ⟨1, 2, 452⟩], triples := #[] }
def er173_669 : Row := { vars := #[116, 280, 641, 131, 640, 639], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 762941, edges := #[⟨3, 4, 218⟩, ⟨3, 5, 219⟩, ⟨4, 5, 460⟩, ⟨0, 3, 105⟩, ⟨1, 3, 465⟩, ⟨1, 4, 80⟩, ⟨2, 4, 458⟩, ⟨1, 5, 81⟩, ⟨2, 5, 459⟩], triples := #[⟨0, 1, 2⟩] }
def er173_670 : Row := { vars := #[203, 280, 578, 654, 560, 233], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 24034, edges := #[⟨3, 4, 406⟩, ⟨3, 5, 335⟩, ⟨4, 5, 261⟩, ⟨1, 3, 123⟩, ⟨2, 3, 394⟩, ⟨1, 4, 9⟩, ⟨2, 4, 469⟩, ⟨0, 5, 155⟩, ⟨1, 5, 408⟩], triples := #[⟨0, 1, 2⟩] }
def er173_671 : Row := { vars := #[203, 280, 578, 546, 233, 678], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 27956, edges := #[⟨3, 4, 281⟩, ⟨3, 5, 406⟩, ⟨4, 5, 315⟩, ⟨1, 3, 45⟩, ⟨2, 3, 491⟩, ⟨0, 4, 155⟩, ⟨1, 4, 408⟩, ⟨1, 5, 111⟩, ⟨2, 5, 384⟩], triples := #[⟨0, 1, 2⟩] }
def er173_672 : Row := { vars := #[280, 400, 499, 553, 167, 583], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 144682, edges := #[⟨3, 4, 311⟩, ⟨3, 5, 502⟩, ⟨4, 5, 279⟩, ⟨0, 3, 64⟩, ⟨2, 3, 91⟩, ⟨0, 4, 498⟩, ⟨1, 4, 429⟩, ⟨0, 5, 160⟩, ⟨2, 5, 19⟩], triples := #[⟨0, 1, 2⟩] }
def er173_673 : Row := { vars := #[280, 400, 499, 588, 636, 495], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 40390, edges := #[⟨3, 4, 433⟩, ⟨3, 5, 6⟩, ⟨4, 5, 41⟩, ⟨0, 3, 151⟩, ⟨1, 3, 131⟩, ⟨0, 4, 175⟩, ⟨1, 4, 100⟩, ⟨0, 5, 273⟩, ⟨2, 5, 342⟩], triples := #[⟨0, 1, 2⟩] }
end HardyCapset20261020.Cert



-- Prove2me | Definitions.Def_HardyCapsetEvaluationData022rows08V420261021
-- name    : HardyCapsetEvaluationData022rows08V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T01:58:30.745476+00:00
-- url     : https://prove2.me/theorems/4391a7f1-1fdf-481c-b84c-dd44fc265599
-- title:
--   HardyCapsetEvaluationData022rows08V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er022_512 : Row := { vars := #[409, 201, 237, 226, 503], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 707367, edges := #[⟨0, 1, 275⟩, ⟨1, 2, 425⟩, ⟨2, 3, 214⟩, ⟨3, 4, 167⟩, ⟨4, 0, 465⟩], triples := #[] }
def er022_513 : Row := { vars := #[32, 108, 226, 503, 538], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 292634, edges := #[⟨0, 1, 148⟩, ⟨1, 2, 496⟩, ⟨2, 3, 167⟩, ⟨3, 4, 424⟩, ⟨4, 0, 347⟩], triples := #[] }
def er022_514 : Row := { vars := #[63, 203, 241, 509, 544], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 284458, edges := #[⟨0, 1, 29⟩, ⟨1, 2, 421⟩, ⟨2, 3, 145⟩, ⟨3, 4, 434⟩, ⟨4, 0, 259⟩], triples := #[] }
def er022_515 : Row := { vars := #[501, 4, 508, 465, 518], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 57226, edges := #[⟨0, 1, 349⟩, ⟨1, 2, 335⟩, ⟨2, 3, 492⟩, ⟨3, 4, 475⟩, ⟨4, 0, 443⟩], triples := #[] }
def er022_516 : Row := { vars := #[15, 362, 426, 573, 554], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 263743, edges := #[⟨0, 1, 445⟩, ⟨1, 2, 94⟩, ⟨2, 3, 441⟩, ⟨3, 4, 496⟩, ⟨4, 0, 285⟩], triples := #[] }
def er022_517 : Row := { vars := #[44, 362, 426, 573, 554], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 375428, edges := #[⟨0, 1, 425⟩, ⟨1, 2, 94⟩, ⟨2, 3, 441⟩, ⟨3, 4, 496⟩, ⟨4, 0, 265⟩], triples := #[] }
def er022_518 : Row := { vars := #[158, 567, 555, 460, 581], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 3457, edges := #[⟨0, 1, 341⟩, ⟨1, 2, 506⟩, ⟨2, 3, 449⟩, ⟨3, 4, 425⟩, ⟨4, 0, 347⟩], triples := #[] }
def er022_519 : Row := { vars := #[562, 34, 555, 460, 581], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 237173, edges := #[⟨0, 1, 261⟩, ⟨1, 2, 275⟩, ⟨2, 3, 449⟩, ⟨3, 4, 425⟩, ⟨4, 0, 510⟩], triples := #[] }
def er022_520 : Row := { vars := #[550, 12, 555, 460, 581], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 482184, edges := #[⟨0, 1, 291⟩, ⟨1, 2, 285⟩, ⟨2, 3, 449⟩, ⟨3, 4, 425⟩, ⟨4, 0, 500⟩], triples := #[] }
def er022_521 : Row := { vars := #[63, 347, 305, 279, 332], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 715543, edges := #[⟨0, 1, 429⟩, ⟨1, 2, 274⟩, ⟨2, 3, 334⟩, ⟨3, 4, 325⟩, ⟨4, 0, 446⟩], triples := #[] }
def er022_522 : Row := { vars := #[471, 159, 279, 332, 220], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 284458, edges := #[⟨0, 1, 297⟩, ⟨1, 2, 457⟩, ⟨2, 3, 325⟩, ⟨3, 4, 336⟩, ⟨4, 0, 57⟩], triples := #[] }
def er022_523 : Row := { vars := #[424, 125, 220, 327, 272], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 715543, edges := #[⟨0, 1, 319⟩, ⟨1, 2, 489⟩, ⟨2, 3, 346⟩, ⟨3, 4, 315⟩, ⟨4, 0, 57⟩], triples := #[] }
def er022_524 : Row := { vars := #[148, 374, 369, 274, 383], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 792067, edges := #[⟨0, 1, 511⟩, ⟨1, 2, 336⟩, ⟨2, 3, 279⟩, ⟨3, 4, 265⟩, ⟨4, 0, 497⟩], triples := #[] }
def er022_525 : Row := { vars := #[359, 22, 369, 274, 383], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 207934, edges := #[⟨0, 1, 441⟩, ⟨1, 2, 455⟩, ⟨2, 3, 279⟩, ⟨3, 4, 265⟩, ⟨4, 0, 350⟩], triples := #[] }
def er022_526 : Row := { vars := #[263, 208, 223, 261, 497], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 360830, edges := #[⟨0, 1, 430⟩, ⟨1, 2, 424⟩, ⟨2, 3, 200⟩, ⟨3, 4, 155⟩, ⟨4, 0, 156⟩], triples := #[] }
def er022_527 : Row := { vars := #[231, 202, 223, 261, 497], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 639171, edges := #[⟨0, 1, 430⟩, ⟨1, 2, 434⟩, ⟨2, 3, 200⟩, ⟨3, 4, 155⟩, ⟨4, 0, 146⟩], triples := #[] }
def er022_528 : Row := { vars := #[254, 168, 446, 566, 554], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 63837, edges := #[⟨0, 1, 447⟩, ⟨1, 2, 287⟩, ⟨2, 3, 441⟩, ⟨3, 4, 506⟩, ⟨4, 0, 79⟩], triples := #[] }
def er022_529 : Row := { vars := #[254, 90, 446, 566, 554], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 296993, edges := #[⟨0, 1, 500⟩, ⟨1, 2, 340⟩, ⟨2, 3, 441⟩, ⟨3, 4, 506⟩, ⟨4, 0, 79⟩], triples := #[] }
def er022_530 : Row := { vars := #[138, 579, 548, 467, 574], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 515609, edges := #[⟨0, 1, 341⟩, ⟨1, 2, 496⟩, ⟨2, 3, 449⟩, ⟨3, 4, 425⟩, ⟨4, 0, 347⟩], triples := #[] }
def er022_531 : Row := { vars := #[557, 41, 548, 467, 574], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 28786, edges := #[⟨0, 1, 261⟩, ⟨1, 2, 275⟩, ⟨2, 3, 449⟩, ⟨3, 4, 425⟩, ⟨4, 0, 500⟩], triples := #[] }
def er022_532 : Row := { vars := #[308, 292, 347, 346, 311, 40, 43], coeff := #[1, 1, 1, 1, 1, 1, 1], bound := 3, weight := 284458, edges := #[⟨0, 1, 312⟩, ⟨1, 2, 339⟩, ⟨2, 3, 286⟩, ⟨3, 4, 264⟩, ⟨4, 5, 475⟩, ⟨5, 6, 52⟩, ⟨6, 0, 479⟩], triples := #[] }
def er022_533 : Row := { vars := #[20, 375, 363, 256, 335], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 237173, edges := #[⟨0, 1, 423⟩, ⟨1, 2, 346⟩, ⟨2, 3, 246⟩, ⟨3, 4, 350⟩, ⟨4, 0, 484⟩], triples := #[] }
def er022_534 : Row := { vars := #[80, 34, 363, 256, 335], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 762828, edges := #[⟨0, 1, 173⟩, ⟨1, 2, 435⟩, ⟨2, 3, 246⟩, ⟨3, 4, 350⟩, ⟨4, 0, 452⟩], triples := #[] }
def er022_535 : Row := { vars := #[35, 345, 232, 371, 406], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000001, edges := #[⟨0, 1, 511⟩, ⟨1, 2, 313⟩, ⟨2, 3, 247⟩, ⟨3, 4, 327⟩, ⟨4, 0, 442⟩], triples := #[] }
def er022_536 : Row := { vars := #[439, 194, 259, 407, 358], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000001, edges := #[⟨0, 1, 270⟩, ⟨1, 2, 420⟩, ⟨2, 3, 275⟩, ⟨3, 4, 317⟩, ⟨4, 0, 106⟩], triples := #[] }
def er022_537 : Row := { vars := #[309, 286, 346, 311, 40], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 715543, edges := #[⟨0, 1, 321⟩, ⟨1, 2, 349⟩, ⟨2, 3, 264⟩, ⟨3, 4, 475⟩, ⟨4, 0, 479⟩], triples := #[] }
def er022_538 : Row := { vars := #[495, 50, 509, 459, 253], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 633946, edges := #[⟨0, 1, 319⟩, ⟨1, 2, 325⟩, ⟨2, 3, 494⟩, ⟨3, 4, 56⟩, ⟨4, 0, 152⟩], triples := #[] }
def er022_539 : Row := { vars := #[42, 74, 459, 253, 392], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 366055, edges := #[⟨0, 1, 172⟩, ⟨1, 2, 350⟩, ⟨2, 3, 56⟩, ⟨3, 4, 260⟩, ⟨4, 0, 456⟩], triples := #[] }
def er022_540 : Row := { vars := #[0, 132, 219, 465, 572], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 942775, edges := #[⟨0, 1, 149⟩, ⟨1, 2, 477⟩, ⟨2, 3, 68⟩, ⟨3, 4, 421⟩, ⟨4, 0, 273⟩], triples := #[] }
def er022_541 : Row := { vars := #[496, 24, 506, 543, 542, 412, 537, 536, 483], coeff := #[1, 1, 1, 1, 1, 1, 1, 1, 1], bound := 4, weight := 1000000, edges := #[⟨0, 1, 335⟩, ⟨1, 2, 349⟩, ⟨2, 3, 430⟩, ⟨3, 4, 452⟩, ⟨4, 5, 473⟩, ⟨5, 6, 483⟩, ⟨6, 7, 442⟩, ⟨7, 8, 495⟩, ⟨8, 0, 481⟩], triples := #[] }
def er022_542 : Row := { vars := #[3, 573, 549, 473, 580], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 288078, edges := #[⟨0, 1, 273⟩, ⟨1, 2, 506⟩, ⟨2, 3, 440⟩, ⟨3, 4, 435⟩, ⟨4, 0, 259⟩], triples := #[] }
def er022_543 : Row := { vars := #[563, 22, 549, 473, 580], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 711923, edges := #[⟨0, 1, 291⟩, ⟨1, 2, 285⟩, ⟨2, 3, 440⟩, ⟨3, 4, 435⟩, ⟨4, 0, 510⟩], triples := #[] }
end HardyCapset20261020.Cert



-- Prove2me | Definitions.Def_HardyCapsetEvaluationData028rows08V420261021
-- name    : HardyCapsetEvaluationData028rows08V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:23:38.663969+00:00
-- url     : https://prove2.me/theorems/bb67b091-a8ad-47da-9c7b-de6552b125b5
-- title:
--   HardyCapsetEvaluationData028rows08V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er028_512 : Row := { vars := #[388, 14, 580, 592, 538], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 11167, edges := #[⟨0, 1, 409⟩, ⟨1, 2, 249⟩, ⟨2, 3, 492⟩, ⟨3, 4, 460⟩, ⟨4, 0, 156⟩], triples := #[] }
def er028_513 : Row := { vars := #[35, 576, 535, 371, 310], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 59120, edges := #[⟨0, 1, 294⟩, ⟨1, 2, 463⟩, ⟨2, 3, 163⟩, ⟨3, 4, 239⟩, ⟨4, 0, 502⟩], triples := #[] }
def er028_514 : Row := { vars := #[331, 123, 537, 481, 261], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 126995, edges := #[⟨0, 1, 380⟩, ⟨1, 2, 208⟩, ⟨2, 3, 375⟩, ⟨3, 4, 107⟩, ⟨4, 0, 231⟩], triples := #[] }
def er028_515 : Row := { vars := #[331, 40, 537, 481, 261], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 822095, edges := #[⟨0, 1, 413⟩, ⟨1, 2, 250⟩, ⟨2, 3, 375⟩, ⟨3, 4, 107⟩, ⟨4, 0, 231⟩], triples := #[] }
def er028_516 : Row := { vars := #[345, 30, 537, 481, 261, 347, 336, 275, 404, 407, 272], coeff := #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], bound := 5, weight := 50912, edges := #[⟨0, 1, 413⟩, ⟨1, 2, 253⟩, ⟨2, 3, 375⟩, ⟨3, 4, 107⟩, ⟨4, 5, 230⟩, ⟨5, 6, 326⟩, ⟨6, 7, 230⟩, ⟨7, 8, 223⟩, ⟨8, 9, 348⟩, ⟨9, 10, 223⟩, ⟨10, 0, 227⟩], triples := #[] }
def er028_517 : Row := { vars := #[52, 168, 495, 402, 316], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 339063, edges := #[⟨0, 1, 90⟩, ⟨1, 2, 218⟩, ⟨2, 3, 50⟩, ⟨3, 4, 243⟩, ⟨4, 0, 504⟩], triples := #[] }
def er028_518 : Row := { vars := #[466, 194, 210, 271, 316, 313, 334], coeff := #[1, 1, 1, 1, 1, 1, 1], bound := 3, weight := 660938, edges := #[⟨0, 1, 207⟩, ⟨1, 2, 186⟩, ⟨2, 3, 379⟩, ⟨3, 4, 253⟩, ⟨4, 5, 294⟩, ⟨5, 6, 211⟩, ⟨6, 0, 24⟩], triples := #[] }
def er028_519 : Row := { vars := #[138, 43, 534, 400, 355], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨0, 1, 117⟩, ⟨1, 2, 250⟩, ⟨2, 3, 136⟩, ⟨3, 4, 306⟩, ⟨4, 0, 502⟩], triples := #[] }
def er028_520 : Row := { vars := #[35, 485, 535, 371, 310], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 508991, edges := #[⟨0, 1, 348⟩, ⟨1, 2, 364⟩, ⟨2, 3, 163⟩, ⟨3, 4, 239⟩, ⟨4, 0, 502⟩], triples := #[] }
def er028_521 : Row := { vars := #[326, 75, 72, 535, 371, 310, 307], coeff := #[1, 1, 1, 1, 1, 1, 1], bound := 3, weight := 431891, edges := #[⟨0, 1, 403⟩, ⟨1, 2, 91⟩, ⟨2, 3, 240⟩, ⟨3, 4, 163⟩, ⟨4, 5, 239⟩, ⟨5, 6, 290⟩, ⟨6, 0, 204⟩], triples := #[] }
def er028_522 : Row := { vars := #[70, 259, 375, 557, 480], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 333334, edges := #[⟨0, 1, 444⟩, ⟨1, 2, 220⟩, ⟨2, 3, 157⟩, ⟨3, 4, 371⟩, ⟨4, 0, 268⟩], triples := #[] }
def er028_523 : Row := { vars := #[55, 106, 375, 557, 480], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 666667, edges := #[⟨0, 1, 158⟩, ⟨1, 2, 366⟩, ⟨2, 3, 157⟩, ⟨3, 4, 371⟩, ⟨4, 0, 338⟩], triples := #[] }
def er028_524 : Row := { vars := #[555, 130, 332, 597, 575], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 217647, edges := #[⟨0, 1, 219⟩, ⟨1, 2, 367⟩, ⟨2, 3, 156⟩, ⟨3, 4, 492⟩, ⟨4, 0, 460⟩], triples := #[] }
def er028_525 : Row := { vars := #[357, 82, 332, 597, 575], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 782354, edges := #[⟨0, 1, 403⟩, ⟨1, 2, 399⟩, ⟨2, 3, 156⟩, ⟨3, 4, 492⟩, ⟨4, 0, 134⟩], triples := #[] }
def er028_526 : Row := { vars := #[295, 177, 487, 594, 477, 583, 564], coeff := #[1, 1, 1, 1, 1, 1, 1], bound := 3, weight := 1000000, edges := #[⟨0, 1, 369⟩, ⟨1, 2, 209⟩, ⟨2, 3, 397⟩, ⟨3, 4, 400⟩, ⟨4, 5, 403⟩, ⟨5, 6, 503⟩, ⟨6, 0, 66⟩], triples := #[] }
def er028_527 : Row := { vars := #[5, 315, 581, 591, 490], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 169060, edges := #[⟨0, 1, 463⟩, ⟨1, 2, 46⟩, ⟨2, 3, 492⟩, ⟨3, 4, 396⟩, ⟨4, 0, 306⟩], triples := #[] }
def er028_528 : Row := { vars := #[15, 298, 581, 591, 490], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 512620, edges := #[⟨0, 1, 463⟩, ⟨1, 2, 59⟩, ⟨2, 3, 492⟩, ⟨3, 4, 396⟩, ⟨4, 0, 303⟩], triples := #[] }
def er028_529 : Row := { vars := #[389, 74, 581, 591, 490], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 318322, edges := #[⟨0, 1, 389⟩, ⟨1, 2, 229⟩, ⟨2, 3, 492⟩, ⟨3, 4, 396⟩, ⟨4, 0, 59⟩], triples := #[] }
def er028_530 : Row := { vars := #[148, 125, 540, 486, 536], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨0, 1, 18⟩, ⟨1, 2, 204⟩, ⟨2, 3, 363⟩, ⟨3, 4, 365⟩, ⟨4, 0, 342⟩], triples := #[] }
def er028_531 : Row := { vars := #[42, 282, 359, 561, 100], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨0, 1, 508⟩, ⟨1, 2, 207⟩, ⟨2, 3, 154⟩, ⟨3, 4, 222⟩, ⟨4, 0, 150⟩], triples := #[] }
def er028_532 : Row := { vars := #[11, 569, 578, 442, 577], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨0, 1, 252⟩, ⟨1, 2, 503⟩, ⟨2, 3, 364⟩, ⟨3, 4, 366⟩, ⟨4, 0, 250⟩], triples := #[] }
def er028_533 : Row := { vars := #[122, 343, 588, 584, 521], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 185229, edges := #[⟨0, 1, 371⟩, ⟨1, 2, 138⟩, ⟨2, 3, 493⟩, ⟨3, 4, 465⟩, ⟨4, 0, 223⟩], triples := #[] }
def er028_534 : Row := { vars := #[385, 91, 588, 584, 521], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 814772, edges := #[⟨0, 1, 380⟩, ⟨1, 2, 208⟩, ⟨2, 3, 493⟩, ⟨3, 4, 465⟩, ⟨4, 0, 163⟩], triples := #[] }
def er028_535 : Row := { vars := #[108, 589, 459, 563, 570], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 573150, edges := #[⟨0, 1, 222⟩, ⟨1, 2, 376⟩, ⟨2, 3, 366⟩, ⟨3, 4, 493⟩, ⟨4, 0, 206⟩], triples := #[] }
def er028_536 : Row := { vars := #[245, 365, 567, 542, 10], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨0, 1, 230⟩, ⟨1, 2, 157⟩, ⟨2, 3, 467⟩, ⟨3, 4, 262⟩, ⟨4, 0, 482⟩], triples := #[] }
def er028_537 : Row := { vars := #[32, 184, 509, 520, 488], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 830469, edges := #[⟨0, 1, 90⟩, ⟨1, 2, 218⟩, ⟨2, 3, 363⟩, ⟨3, 4, 379⟩, ⟨4, 0, 348⟩], triples := #[] }
def er028_538 : Row := { vars := #[60, 44, 238, 520, 488], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 169532, edges := #[⟨0, 1, 177⟩, ⟨1, 2, 467⟩, ⟨2, 3, 4⟩, ⟨3, 4, 379⟩, ⟨4, 0, 272⟩], triples := #[] }
def er028_539 : Row := { vars := #[260, 192, 265, 489, 529], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 782354, edges := #[⟨0, 1, 379⟩, ⟨1, 2, 371⟩, ⟨2, 3, 77⟩, ⟨3, 4, 375⟩, ⟨4, 0, 34⟩], triples := #[] }
def er028_540 : Row := { vars := #[246, 163, 265, 489, 529], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 217647, edges := #[⟨0, 1, 399⟩, ⟨1, 2, 403⟩, ⟨2, 3, 77⟩, ⟨3, 4, 375⟩, ⟨4, 0, 14⟩], triples := #[] }
def er028_541 : Row := { vars := #[465, 3, 459, 563, 570], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 426851, edges := #[⟨0, 1, 316⟩, ⟨1, 2, 320⟩, ⟨2, 3, 366⟩, ⟨3, 4, 493⟩, ⟨4, 0, 368⟩], triples := #[] }
end HardyCapset20261020.Cert



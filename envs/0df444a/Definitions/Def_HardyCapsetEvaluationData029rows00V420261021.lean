-- Prove2me | Definitions.Def_HardyCapsetEvaluationData029rows00V420261021
-- name    : HardyCapsetEvaluationData029rows00V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:29:34.89024+00:00
-- url     : https://prove2.me/theorems/3e61ee52-929a-4f1e-b2a9-bed8f7630460
-- title:
--   HardyCapsetEvaluationData029rows00V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er029_000 : Row := { vars := #[38, 221], coeff := #[1, 1], bound := 1, weight := 17655, edges := #[⟨0, 1, 384⟩], triples := #[] }
def er029_001 : Row := { vars := #[78, 240], coeff := #[1, 1], bound := 1, weight := 622141, edges := #[⟨0, 1, 436⟩], triples := #[] }
def er029_002 : Row := { vars := #[109, 150], coeff := #[1, 1], bound := 1, weight := 157654, edges := #[⟨0, 1, 37⟩], triples := #[] }
def er029_003 : Row := { vars := #[201, 374], coeff := #[1, 1], bound := 1, weight := 107236, edges := #[⟨0, 1, 168⟩], triples := #[] }
def er029_004 : Row := { vars := #[237, 253], coeff := #[1, 1], bound := 1, weight := 162985, edges := #[⟨0, 1, 260⟩], triples := #[] }
def er029_005 : Row := { vars := #[260, 272], coeff := #[1, 1], bound := 1, weight := 76438, edges := #[⟨0, 1, 286⟩], triples := #[] }
def er029_006 : Row := { vars := #[262, 367], coeff := #[1, 1], bound := 1, weight := 100894, edges := #[⟨0, 1, 72⟩], triples := #[] }
def er029_007 : Row := { vars := #[278, 284], coeff := #[1, 1], bound := 1, weight := 84572, edges := #[⟨0, 1, 340⟩], triples := #[] }
def er029_008 : Row := { vars := #[310, 336], coeff := #[1, 1], bound := 1, weight := 250363, edges := #[⟨0, 1, 81⟩], triples := #[] }
def er029_009 : Row := { vars := #[310, 390], coeff := #[1, 1], bound := 1, weight := 33587, edges := #[⟨0, 1, 171⟩], triples := #[] }
def er029_010 : Row := { vars := #[321, 357], coeff := #[1, 1], bound := 1, weight := 259645, edges := #[⟨0, 1, 506⟩], triples := #[] }
def er029_011 : Row := { vars := #[325, 353], coeff := #[1, 1], bound := 1, weight := 31257, edges := #[⟨0, 1, 497⟩], triples := #[] }
def er029_012 : Row := { vars := #[7, 211, 331], coeff := #[1, 1, 1], bound := 2, weight := 33141, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er029_013 : Row := { vars := #[135, 205, 393], coeff := #[1, 1, 1], bound := 2, weight := 334392, edges := #[], triples := #[⟨0, 1, 2⟩] }
def er029_014 : Row := { vars := #[9, 13, 288, 402], coeff := #[1, 1, 1, 1], bound := 1, weight := 18361, edges := #[⟨0, 1, 8⟩, ⟨0, 2, 427⟩, ⟨0, 3, 267⟩, ⟨1, 2, 433⟩, ⟨1, 3, 273⟩, ⟨2, 3, 175⟩], triples := #[] }
def er029_015 : Row := { vars := #[14, 153, 119], coeff := #[1, 1, 1], bound := 1, weight := 98208, edges := #[⟨0, 1, 130⟩, ⟨0, 2, 140⟩, ⟨1, 2, 32⟩], triples := #[] }
def er029_016 : Row := { vars := #[18, 280, 354], coeff := #[1, 1, 1], bound := 1, weight := 127205, edges := #[⟨0, 1, 431⟩, ⟨0, 2, 323⟩, ⟨1, 2, 2⟩], triples := #[] }
def er029_017 : Row := { vars := #[18, 408, 246], coeff := #[1, 1, 1], bound := 1, weight := 438601, edges := #[⟨0, 1, 255⟩, ⟨0, 2, 478⟩, ⟨1, 2, 2⟩], triples := #[] }
def er029_018 : Row := { vars := #[19, 402, 239], coeff := #[1, 1, 1], bound := 1, weight := 11313, edges := #[⟨0, 1, 263⟩, ⟨0, 2, 485⟩, ⟨1, 2, 33⟩], triples := #[] }
def er029_019 : Row := { vars := #[20, 407, 312], coeff := #[1, 1, 1], bound := 1, weight := 72220, edges := #[⟨0, 1, 254⟩, ⟨0, 2, 405⟩, ⟨1, 2, 165⟩], triples := #[] }
def er029_020 : Row := { vars := #[20, 282, 354], coeff := #[1, 1, 1], bound := 1, weight := 391797, edges := #[⟨0, 1, 431⟩, ⟨0, 2, 325⟩, ⟨1, 2, 4⟩], triples := #[] }
def er029_021 : Row := { vars := #[25, 289, 422], coeff := #[1, 1, 1], bound := 1, weight := 454053, edges := #[⟨0, 1, 414⟩, ⟨0, 2, 245⟩, ⟨1, 2, 162⟩], triples := #[] }
def er029_022 : Row := { vars := #[28, 22, 27, 244, 342], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 437452, edges := #[⟨0, 1, 10⟩, ⟨0, 2, 2⟩, ⟨0, 3, 469⟩, ⟨0, 4, 192⟩, ⟨1, 2, 19⟩, ⟨1, 3, 477⟩, ⟨1, 4, 209⟩, ⟨2, 3, 473⟩, ⟨2, 4, 205⟩, ⟨3, 4, 149⟩], triples := #[] }
def er029_023 : Row := { vars := #[42, 297, 335, 57, 52], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 87378, edges := #[⟨0, 1, 437⟩, ⟨0, 2, 215⟩, ⟨0, 3, 67⟩, ⟨0, 4, 70⟩, ⟨1, 2, 100⟩, ⟨1, 3, 453⟩, ⟨1, 4, 457⟩, ⟨2, 3, 204⟩, ⟨2, 4, 208⟩, ⟨3, 4, 54⟩], triples := #[] }
def er029_024 : Row := { vars := #[43, 264, 417], coeff := #[1, 1, 1], bound := 1, weight := 112090, edges := #[⟨0, 1, 511⟩, ⟨0, 2, 277⟩, ⟨1, 2, 66⟩], triples := #[] }
def er029_025 : Row := { vars := #[43, 243, 378], coeff := #[1, 1, 1], bound := 1, weight := 104738, edges := #[⟨0, 1, 458⟩, ⟨0, 2, 351⟩, ⟨1, 2, 102⟩], triples := #[] }
def er029_026 : Row := { vars := #[45, 138, 275, 389], coeff := #[1, 1, 1, 1], bound := 1, weight := 146788, edges := #[⟨0, 1, 110⟩, ⟨0, 2, 434⟩, ⟨0, 3, 274⟩, ⟨1, 2, 465⟩, ⟨1, 3, 305⟩, ⟨2, 3, 150⟩], triples := #[] }
def er029_027 : Row := { vars := #[46, 168, 269], coeff := #[1, 1, 1], bound := 1, weight := 201628, edges := #[⟨0, 1, 72⟩, ⟨0, 2, 500⟩, ⟨1, 2, 365⟩], triples := #[] }
def er029_028 : Row := { vars := #[46, 312, 383], coeff := #[1, 1, 1], bound := 1, weight := 531293, edges := #[⟨0, 1, 445⟩, ⟨0, 2, 340⟩, ⟨1, 2, 69⟩], triples := #[] }
def er029_029 : Row := { vars := #[49, 299, 91], coeff := #[1, 1, 1], bound := 1, weight := 236136, edges := #[⟨0, 1, 451⟩, ⟨0, 2, 171⟩, ⟨1, 2, 390⟩], triples := #[] }
def er029_030 : Row := { vars := #[50, 412, 109], coeff := #[1, 1, 1], bound := 1, weight := 43015, edges := #[⟨0, 1, 293⟩, ⟨0, 2, 140⟩, ⟨1, 2, 208⟩], triples := #[] }
def er029_031 : Row := { vars := #[50, 295, 420], coeff := #[1, 1, 1], bound := 1, weight := 201948, edges := #[⟨0, 1, 404⟩, ⟨0, 2, 286⟩, ⟨1, 2, 134⟩], triples := #[] }
def er029_032 : Row := { vars := #[51, 298, 106], coeff := #[1, 1, 1], bound := 1, weight := 331865, edges := #[⟨0, 1, 451⟩, ⟨0, 2, 149⟩, ⟨1, 2, 375⟩], triples := #[] }
def er029_033 : Row := { vars := #[56, 381, 305], coeff := #[1, 1, 1], bound := 1, weight := 315167, edges := #[⟨0, 1, 330⟩, ⟨0, 2, 443⟩, ⟨1, 2, 48⟩], triples := #[] }
def er029_034 : Row := { vars := #[71, 272, 270], coeff := #[1, 1, 1], bound := 1, weight := 167856, edges := #[⟨0, 1, 419⟩, ⟨0, 2, 422⟩, ⟨1, 2, 296⟩], triples := #[] }
def er029_035 : Row := { vars := #[74, 10, 123], coeff := #[1, 1, 1], bound := 1, weight := 64275, edges := #[⟨0, 1, 183⟩, ⟨0, 2, 118⟩, ⟨1, 2, 163⟩], triples := #[] }
def er029_036 : Row := { vars := #[76, 249, 381], coeff := #[1, 1, 1], bound := 1, weight := 213401, edges := #[⟨0, 1, 443⟩, ⟨0, 2, 261⟩, ⟨1, 2, 104⟩], triples := #[] }
def er029_037 : Row := { vars := #[77, 360, 168, 246], coeff := #[1, 1, 1, 1], bound := 1, weight := 107791, edges := #[⟨0, 1, 291⟩, ⟨0, 2, 36⟩, ⟨0, 3, 451⟩, ⟨1, 2, 231⟩, ⟨1, 3, 115⟩, ⟨2, 3, 391⟩], triples := #[] }
def er029_038 : Row := { vars := #[78, 395, 227], coeff := #[1, 1, 1], bound := 1, weight := 332407, edges := #[⟨0, 1, 234⟩, ⟨0, 2, 484⟩, ⟨1, 2, 106⟩], triples := #[] }
def er029_039 : Row := { vars := #[80, 269, 425], coeff := #[1, 1, 1], bound := 1, weight := 281473, edges := #[⟨0, 1, 415⟩, ⟨0, 2, 225⟩, ⟨1, 2, 71⟩], triples := #[] }
def er029_040 : Row := { vars := #[82, 258, 335], coeff := #[1, 1, 1], bound := 1, weight := 326459, edges := #[⟨0, 1, 431⟩, ⟨0, 2, 341⟩, ⟨1, 2, 167⟩], triples := #[] }
def er029_041 : Row := { vars := #[87, 60, 243], coeff := #[1, 1, 1], bound := 1, weight := 16653, edges := #[⟨0, 1, 168⟩, ⟨0, 2, 457⟩, ⟨1, 2, 463⟩], triples := #[] }
def er029_042 : Row := { vars := #[90, 386, 263, 186], coeff := #[1, 1, 1, 1], bound := 1, weight := 141289, edges := #[⟨0, 1, 269⟩, ⟨0, 2, 416⟩, ⟨0, 3, 10⟩, ⟨1, 2, 121⟩, ⟨1, 3, 234⟩, ⟨2, 3, 400⟩], triples := #[] }
def er029_043 : Row := { vars := #[90, 83, 358, 88], coeff := #[1, 1, 1, 1], bound := 1, weight := 43005, edges := #[⟨0, 1, 84⟩, ⟨0, 2, 276⟩, ⟨0, 3, 76⟩, ⟨1, 2, 286⟩, ⟨1, 3, 90⟩, ⟨2, 3, 282⟩], triples := #[] }
def er029_044 : Row := { vars := #[136, 314, 313], coeff := #[1, 1, 1], bound := 1, weight := 46051, edges := #[⟨0, 1, 474⟩, ⟨0, 2, 476⟩, ⟨1, 2, 351⟩], triples := #[] }
def er029_045 : Row := { vars := #[140, 303, 401], coeff := #[1, 1, 1], bound := 1, weight := 84898, edges := #[⟨0, 1, 468⟩, ⟨0, 2, 351⟩, ⟨1, 2, 163⟩], triples := #[] }
def er029_046 : Row := { vars := #[141, 40, 106], coeff := #[1, 1, 1], bound := 1, weight := 17251, edges := #[⟨0, 1, 110⟩, ⟨0, 2, 64⟩, ⟨1, 2, 164⟩], triples := #[] }
def er029_047 : Row := { vars := #[142, 22, 407], coeff := #[1, 1, 1], bound := 1, weight := 141498, edges := #[⟨0, 1, 131⟩, ⟨0, 2, 340⟩, ⟨1, 2, 256⟩], triples := #[] }
def er029_048 : Row := { vars := #[143, 293, 119], coeff := #[1, 1, 1], bound := 1, weight := 568664, edges := #[⟨0, 1, 499⟩, ⟨0, 2, 0⟩, ⟨1, 2, 367⟩], triples := #[] }
def er029_049 : Row := { vars := #[145, 171, 190], coeff := #[1, 1, 1], bound := 1, weight := 144606, edges := #[⟨0, 1, 184⟩, ⟨0, 2, 170⟩, ⟨1, 2, 134⟩], triples := #[] }
def er029_050 : Row := { vars := #[202, 394, 124], coeff := #[1, 1, 1], bound := 1, weight := 18595, edges := #[⟨0, 1, 123⟩, ⟨0, 2, 483⟩, ⟨1, 2, 213⟩], triples := #[] }
def er029_051 : Row := { vars := #[205, 366, 187], coeff := #[1, 1, 1], bound := 1, weight := 187106, edges := #[⟨0, 1, 181⟩, ⟨0, 2, 424⟩, ⟨1, 2, 192⟩], triples := #[] }
def er029_052 : Row := { vars := #[208, 261, 173], coeff := #[1, 1, 1], bound := 1, weight := 252913, edges := #[⟨0, 1, 325⟩, ⟨0, 2, 437⟩, ⟨1, 2, 366⟩], triples := #[] }
def er029_053 : Row := { vars := #[211, 258, 290], coeff := #[1, 1, 1], bound := 1, weight := 28667, edges := #[⟨0, 1, 314⟩, ⟨0, 2, 293⟩, ⟨1, 2, 205⟩], triples := #[] }
def er029_054 : Row := { vars := #[212, 298, 247], coeff := #[1, 1, 1], bound := 1, weight := 127080, edges := #[⟨0, 1, 259⟩, ⟨0, 2, 345⟩, ⟨1, 2, 206⟩], triples := #[] }
def er029_055 : Row := { vars := #[213, 249, 300], coeff := #[1, 1, 1], bound := 1, weight := 168558, edges := #[⟨0, 1, 347⟩, ⟨0, 2, 261⟩, ⟨1, 2, 207⟩], triples := #[] }
def er029_056 : Row := { vars := #[215, 396, 126], coeff := #[1, 1, 1], bound := 1, weight := 92518, edges := #[⟨0, 1, 125⟩, ⟨0, 2, 485⟩, ⟨1, 2, 208⟩], triples := #[] }
def er029_057 : Row := { vars := #[218, 243, 313], coeff := #[1, 1, 1], bound := 1, weight := 366462, edges := #[⟨0, 1, 341⟩, ⟨0, 2, 275⟩, ⟨1, 2, 211⟩], triples := #[] }
def er029_058 : Row := { vars := #[220, 366, 381], coeff := #[1, 1, 1], bound := 1, weight := 329588, edges := #[⟨0, 1, 168⟩, ⟨0, 2, 141⟩, ⟨1, 2, 411⟩], triples := #[] }
def er029_059 : Row := { vars := #[223, 72, 426], coeff := #[1, 1, 1], bound := 1, weight := 345723, edges := #[⟨0, 1, 500⟩, ⟨0, 2, 100⟩, ⟨1, 2, 229⟩], triples := #[] }
def er029_060 : Row := { vars := #[225, 307, 348], coeff := #[1, 1, 1], bound := 1, weight := 50067, edges := #[⟨0, 1, 285⟩, ⟨0, 2, 178⟩, ⟨1, 2, 11⟩], triples := #[] }
def er029_061 : Row := { vars := #[230, 303, 313], coeff := #[1, 1, 1], bound := 1, weight := 393987, edges := #[⟨0, 1, 285⟩, ⟨0, 2, 295⟩, ⟨1, 2, 342⟩], triples := #[] }
def er029_062 : Row := { vars := #[235, 258, 247], coeff := #[1, 1, 1], bound := 1, weight := 425090, edges := #[⟨0, 1, 259⟩, ⟨0, 2, 293⟩, ⟨1, 2, 249⟩], triples := #[] }
def er029_063 : Row := { vars := #[235, 40, 409], coeff := #[1, 1, 1], bound := 1, weight := 30700, edges := #[⟨0, 1, 479⟩, ⟨0, 2, 64⟩, ⟨1, 2, 249⟩], triples := #[] }
end HardyCapset20261020.Cert



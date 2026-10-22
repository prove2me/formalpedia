-- Prove2me | Definitions.Def_HardyCapsetEvaluationData173rows01V420261021
-- name    : HardyCapsetEvaluationData173rows01V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:07:46.159612+00:00
-- url     : https://prove2.me/theorems/2670746f-77e5-469f-aac2-f71603c7ad20
-- title:
--   HardyCapsetEvaluationData173rows01V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er173_064 : Row := { vars := #[20, 51, 24, 26], coeff := #[1, 1, 1, 1], bound := 1, weight := 128689, edges := #[⟨0, 1, 18⟩, ⟨0, 2, 11⟩, ⟨0, 3, 12⟩, ⟨1, 2, 24⟩, ⟨1, 3, 25⟩, ⟨2, 3, 5⟩], triples := #[] }
def er173_065 : Row := { vars := #[20, 317, 489, 340], coeff := #[1, 1, 1, 1], bound := 1, weight := 31947, edges := #[⟨0, 1, 384⟩, ⟨0, 2, 406⟩, ⟨0, 3, 355⟩, ⟨1, 2, 246⟩, ⟨1, 3, 195⟩, ⟨2, 3, 279⟩], triples := #[] }
def er173_066 : Row := { vars := #[21, 23, 262], coeff := #[1, 1, 1], bound := 1, weight := 271695, edges := #[⟨0, 1, 9⟩, ⟨0, 2, 83⟩, ⟨1, 2, 75⟩], triples := #[] }
def er173_067 : Row := { vars := #[21, 37, 176, 24], coeff := #[1, 1, 1, 1], bound := 1, weight := 281602, edges := #[⟨0, 1, 29⟩, ⟨0, 2, 142⟩, ⟨0, 3, 10⟩, ⟨1, 2, 165⟩, ⟨1, 3, 33⟩, ⟨2, 3, 138⟩], triples := #[] }
def er173_068 : Row := { vars := #[21, 52, 24, 176], coeff := #[1, 1, 1, 1], bound := 1, weight := 109459, edges := #[⟨0, 1, 19⟩, ⟨0, 2, 10⟩, ⟨0, 3, 142⟩, ⟨1, 2, 23⟩, ⟨1, 3, 155⟩, ⟨2, 3, 138⟩], triples := #[] }
def er173_069 : Row := { vars := #[21, 318, 386, 384], coeff := #[1, 1, 1, 1], bound := 1, weight := 249327, edges := #[⟨0, 1, 385⟩, ⟨0, 2, 489⟩, ⟨0, 3, 488⟩, ⟨1, 2, 329⟩, ⟨1, 3, 328⟩, ⟨2, 3, 260⟩], triples := #[] }
def er173_070 : Row := { vars := #[21, 318, 371, 511], coeff := #[1, 1, 1, 1], bound := 1, weight := 87919, edges := #[⟨0, 1, 385⟩, ⟨0, 2, 502⟩, ⟨0, 3, 410⟩, ⟨1, 2, 342⟩, ⟨1, 3, 250⟩, ⟨2, 3, 232⟩], triples := #[] }
def er173_071 : Row := { vars := #[22, 281, 294, 175], coeff := #[1, 1, 1, 1], bound := 1, weight := 514201, edges := #[⟨0, 1, 394⟩, ⟨0, 2, 403⟩, ⟨0, 3, 135⟩, ⟨1, 2, 219⟩, ⟨1, 3, 470⟩, ⟨2, 3, 489⟩], triples := #[] }
def er173_072 : Row := { vars := #[22, 219, 234], coeff := #[1, 1, 1], bound := 1, weight := 136065, edges := #[⟨0, 1, 130⟩, ⟨0, 2, 126⟩, ⟨1, 2, 143⟩], triples := #[] }
def er173_073 : Row := { vars := #[23, 393, 380, 262], coeff := #[1, 1, 1, 1], bound := 1, weight := 291383, edges := #[⟨0, 1, 477⟩, ⟨0, 2, 469⟩, ⟨0, 3, 75⟩, ⟨1, 2, 260⟩, ⟨1, 3, 369⟩, ⟨2, 3, 352⟩], triples := #[] }
def er173_074 : Row := { vars := #[23, 272, 147], coeff := #[1, 1, 1], bound := 1, weight := 251973, edges := #[⟨0, 1, 101⟩, ⟨0, 2, 186⟩, ⟨1, 2, 10⟩], triples := #[] }
def er173_075 : Row := { vars := #[24, 259, 25, 268], coeff := #[1, 1, 1, 1], bound := 1, weight := 116331, edges := #[⟨0, 1, 83⟩, ⟨0, 2, 6⟩, ⟨0, 3, 106⟩, ⟨1, 2, 82⟩, ⟨1, 3, 191⟩, ⟨2, 3, 105⟩], triples := #[] }
def er173_076 : Row := { vars := #[24, 263, 449, 649, 25, 444], coeff := #[1, 1, 1, 1, 1, 1], bound := 1, weight := 883670, edges := #[⟨0, 1, 78⟩, ⟨0, 2, 447⟩, ⟨0, 3, 283⟩, ⟨0, 4, 6⟩, ⟨0, 5, 457⟩, ⟨1, 2, 479⟩, ⟨1, 3, 315⟩, ⟨1, 4, 77⟩, ⟨1, 5, 489⟩, ⟨2, 3, 165⟩, ⟨2, 4, 445⟩, ⟨2, 5, 300⟩, ⟨3, 4, 281⟩, ⟨3, 5, 142⟩, ⟨4, 5, 455⟩], triples := #[] }
def er173_077 : Row := { vars := #[26, 258, 274], coeff := #[1, 1, 1], bound := 1, weight := 172846, edges := #[⟨0, 1, 83⟩, ⟨0, 2, 96⟩, ⟨1, 2, 186⟩], triples := #[] }
def er173_078 : Row := { vars := #[26, 260, 459, 308], coeff := #[1, 1, 1, 1], bound := 1, weight := 561294, edges := #[⟨0, 1, 75⟩, ⟨0, 2, 416⟩, ⟨0, 3, 400⟩, ⟨1, 2, 459⟩, ⟨1, 3, 425⟩, ⟨2, 3, 281⟩], triples := #[] }
def er173_079 : Row := { vars := #[26, 463, 586, 473], coeff := #[1, 1, 1, 1], bound := 1, weight := 137173, edges := #[⟨0, 1, 433⟩, ⟨0, 2, 335⟩, ⟨0, 3, 423⟩, ⟨1, 2, 46⟩, ⟨1, 3, 310⟩, ⟨2, 3, 69⟩], triples := #[] }
def er173_080 : Row := { vars := #[27, 265, 442, 28], coeff := #[1, 1, 1, 1], bound := 1, weight := 491295, edges := #[⟨0, 1, 83⟩, ⟨0, 2, 453⟩, ⟨0, 3, 11⟩, ⟨1, 2, 485⟩, ⟨1, 3, 82⟩, ⟨2, 3, 451⟩], triples := #[] }
def er173_081 : Row := { vars := #[27, 29, 178, 361], coeff := #[1, 1, 1, 1], bound := 1, weight := 508706, edges := #[⟨0, 1, 10⟩, ⟨0, 2, 143⟩, ⟨0, 3, 506⟩, ⟨1, 2, 142⟩, ⟨1, 3, 505⟩, ⟨2, 3, 431⟩], triples := #[] }
def er173_082 : Row := { vars := #[28, 177, 204], coeff := #[1, 1, 1], bound := 1, weight := 215287, edges := #[⟨0, 1, 143⟩, ⟨0, 2, 122⟩, ⟨1, 2, 8⟩], triples := #[] }
def er173_083 : Row := { vars := #[28, 468, 607], coeff := #[1, 1, 1], bound := 1, weight := 293419, edges := #[⟨0, 1, 427⟩, ⟨0, 2, 314⟩, ⟨1, 2, 8⟩], triples := #[] }
def er173_084 : Row := { vars := #[29, 264, 117], coeff := #[1, 1, 1], bound := 1, weight := 45764, edges := #[⟨0, 1, 83⟩, ⟨0, 2, 182⟩, ⟨1, 2, 9⟩], triples := #[] }
def er173_085 : Row := { vars := #[29, 659, 400], coeff := #[1, 1, 1], bound := 1, weight := 278292, edges := #[⟨0, 1, 268⟩, ⟨0, 2, 472⟩, ⟨1, 2, 9⟩], triples := #[] }
def er173_086 : Row := { vars := #[29, 670, 387], coeff := #[1, 1, 1], bound := 1, weight := 15618, edges := #[⟨0, 1, 259⟩, ⟨0, 2, 481⟩, ⟨1, 2, 9⟩], triples := #[] }
def er173_087 : Row := { vars := #[29, 585, 347], coeff := #[1, 1, 1], bound := 1, weight := 151623, edges := #[⟨0, 1, 335⟩, ⟨0, 2, 372⟩, ⟨1, 2, 170⟩], triples := #[] }
def er173_088 : Row := { vars := #[30, 182, 574], coeff := #[1, 1, 1], bound := 1, weight := 119367, edges := #[⟨0, 1, 160⟩, ⟨0, 2, 211⟩, ⟨1, 2, 333⟩], triples := #[] }
def er173_089 : Row := { vars := #[30, 59, 45], coeff := #[1, 1, 1], bound := 1, weight := 880634, edges := #[⟨0, 1, 24⟩, ⟨0, 2, 33⟩, ⟨1, 2, 11⟩], triples := #[] }
def er173_090 : Row := { vars := #[31, 192, 46], coeff := #[1, 1, 1], bound := 1, weight := 533485, edges := #[⟨0, 1, 156⟩, ⟨0, 2, 34⟩, ⟨1, 2, 143⟩], triples := #[] }
def er173_091 : Row := { vars := #[32, 47, 62], coeff := #[1, 1, 1], bound := 1, weight := 439236, edges := #[⟨0, 1, 35⟩, ⟨0, 2, 25⟩, ⟨1, 2, 12⟩], triples := #[] }
def er173_092 : Row := { vars := #[32, 573, 636], coeff := #[1, 1, 1], bound := 1, weight := 314493, edges := #[⟨0, 1, 209⟩, ⟨0, 2, 304⟩, ⟨1, 2, 509⟩], triples := #[] }
def er173_093 : Row := { vars := #[33, 38, 276], coeff := #[1, 1, 1], bound := 1, weight := 53879, edges := #[⟨0, 1, 23⟩, ⟨0, 2, 84⟩, ⟨1, 2, 76⟩], triples := #[] }
def er173_094 : Row := { vars := #[33, 38, 56], coeff := #[1, 1, 1], bound := 1, weight := 48530, edges := #[⟨0, 1, 23⟩, ⟨0, 2, 10⟩, ⟨1, 2, 2⟩], triples := #[] }
def er173_095 : Row := { vars := #[33, 38, 191], coeff := #[1, 1, 1], bound := 1, weight := 686736, edges := #[⟨0, 1, 23⟩, ⟨0, 2, 143⟩, ⟨1, 2, 135⟩], triples := #[] }
def er173_096 : Row := { vars := #[33, 570, 336], coeff := #[1, 1, 1], bound := 1, weight := 88131, edges := #[⟨0, 1, 199⟩, ⟨0, 2, 374⟩, ⟨1, 2, 55⟩], triples := #[] }
def er173_097 : Row := { vars := #[33, 369, 123], coeff := #[1, 1, 1], bound := 1, weight := 122727, edges := #[⟨0, 1, 492⟩, ⟨0, 2, 187⟩, ⟨1, 2, 404⟩], triples := #[] }
def er173_098 : Row := { vars := #[34, 648, 455], coeff := #[1, 1, 1], bound := 1, weight := 439785, edges := #[⟨0, 1, 279⟩, ⟨0, 2, 427⟩, ⟨1, 2, 186⟩], triples := #[] }
def er173_099 : Row := { vars := #[34, 39, 277], coeff := #[1, 1, 1], bound := 1, weight := 490088, edges := #[⟨0, 1, 24⟩, ⟨0, 2, 83⟩, ⟨1, 2, 75⟩], triples := #[] }
def er173_100 : Row := { vars := #[34, 181, 350], coeff := #[1, 1, 1], bound := 1, weight := 70128, edges := #[⟨0, 1, 151⟩, ⟨0, 2, 354⟩, ⟨1, 2, 491⟩], triples := #[] }
def er173_101 : Row := { vars := #[35, 58, 40], coeff := #[1, 1, 1], bound := 1, weight := 966691, edges := #[⟨0, 1, 12⟩, ⟨0, 2, 25⟩, ⟨1, 2, 4⟩], triples := #[] }
def er173_102 : Row := { vars := #[35, 58, 159], coeff := #[1, 1, 1], bound := 1, weight := 33310, edges := #[⟨0, 1, 12⟩, ⟨0, 2, 175⟩, ⟨1, 2, 171⟩], triples := #[] }
def er173_103 : Row := { vars := #[36, 266, 385, 569], coeff := #[1, 1, 1, 1], bound := 1, weight := 114605, edges := #[⟨0, 1, 90⟩, ⟨0, 2, 479⟩, ⟨0, 3, 193⟩, ⟨1, 2, 370⟩, ⟨1, 3, 279⟩, ⟨2, 3, 143⟩], triples := #[] }
def er173_104 : Row := { vars := #[36, 142, 119], coeff := #[1, 1, 1], bound := 1, weight := 198946, edges := #[⟨0, 1, 183⟩, ⟨0, 2, 187⟩, ⟨1, 2, 82⟩], triples := #[] }
def er173_105 : Row := { vars := #[36, 190, 579], coeff := #[1, 1, 1], bound := 1, weight := 408990, edges := #[⟨0, 1, 141⟩, ⟨0, 2, 349⟩, ⟨1, 2, 260⟩], triples := #[] }
def er173_106 : Row := { vars := #[36, 207, 369], coeff := #[1, 1, 1], bound := 1, weight := 81569, edges := #[⟨0, 1, 126⟩, ⟨0, 2, 491⟩, ⟨1, 2, 354⟩], triples := #[] }
def er173_107 : Row := { vars := #[37, 642, 255], coeff := #[1, 1, 1], bound := 1, weight := 321016, edges := #[⟨0, 1, 295⟩, ⟨0, 2, 110⟩, ⟨1, 2, 336⟩], triples := #[] }
def er173_108 : Row := { vars := #[37, 476, 255], coeff := #[1, 1, 1], bound := 1, weight := 392261, edges := #[⟨0, 1, 414⟩, ⟨0, 2, 110⟩, ⟨1, 2, 488⟩], triples := #[] }
def er173_109 : Row := { vars := #[38, 266, 56], coeff := #[1, 1, 1], bound := 1, weight := 210858, edges := #[⟨0, 1, 95⟩, ⟨0, 2, 2⟩, ⟨1, 2, 82⟩], triples := #[] }
def er173_110 : Row := { vars := #[39, 179, 57], coeff := #[1, 1, 1], bound := 1, weight := 509913, edges := #[⟨0, 1, 155⟩, ⟨0, 2, 3⟩, ⟨1, 2, 142⟩], triples := #[] }
def er173_111 : Row := { vars := #[40, 653, 577, 638], coeff := #[1, 1, 1, 1], bound := 1, weight := 33310, edges := #[⟨0, 1, 274⟩, ⟨0, 2, 350⟩, ⟨0, 3, 295⟩, ⟨1, 2, 396⟩, ⟨1, 3, 492⟩, ⟨2, 3, 353⟩], triples := #[] }
def er173_112 : Row := { vars := #[41, 54, 49], coeff := #[1, 1, 1], bound := 1, weight := 414492, edges := #[⟨0, 1, 2⟩, ⟨0, 2, 10⟩, ⟨1, 2, 34⟩], triples := #[] }
def er173_113 : Row := { vars := #[41, 698, 205], coeff := #[1, 1, 1], bound := 1, weight := 244883, edges := #[⟨0, 1, 247⟩, ⟨0, 2, 131⟩, ⟨1, 2, 320⟩], triples := #[] }
def er173_114 : Row := { vars := #[41, 328, 494], coeff := #[1, 1, 1], bound := 1, weight := 340627, edges := #[⟨0, 1, 389⟩, ⟨0, 2, 410⟩, ⟨1, 2, 250⟩], triples := #[] }
def er173_115 : Row := { vars := #[42, 522, 337, 440], coeff := #[1, 1, 1, 1], bound := 1, weight := 261749, edges := #[⟨0, 1, 242⟩, ⟨0, 2, 383⟩, ⟨0, 3, 455⟩, ⟨1, 2, 9⟩, ⟨1, 3, 83⟩, ⟨2, 3, 256⟩], triples := #[] }
def er173_116 : Row := { vars := #[42, 291, 299], coeff := #[1, 1, 1], bound := 1, weight := 364873, edges := #[⟨0, 1, 400⟩, ⟨0, 2, 399⟩, ⟨1, 2, 209⟩], triples := #[] }
def er173_117 : Row := { vars := #[42, 53, 273], coeff := #[1, 1, 1], bound := 1, weight := 352196, edges := #[⟨0, 1, 2⟩, ⟨0, 2, 82⟩, ⟨1, 2, 105⟩], triples := #[] }
def er173_118 : Row := { vars := #[42, 53, 372, 377], coeff := #[1, 1, 1, 1], bound := 1, weight := 21184, edges := #[⟨0, 1, 2⟩, ⟨0, 2, 492⟩, ⟨0, 3, 488⟩, ⟨1, 2, 503⟩, ⟨1, 3, 478⟩, ⟨2, 3, 281⟩], triples := #[] }
def er173_119 : Row := { vars := #[43, 404, 574], coeff := #[1, 1, 1], bound := 1, weight := 219859, edges := #[⟨0, 1, 469⟩, ⟨0, 2, 199⟩, ⟨1, 2, 166⟩], triples := #[] }
def er173_120 : Row := { vars := #[43, 54, 453, 458], coeff := #[1, 1, 1, 1], bound := 1, weight := 309282, edges := #[⟨0, 1, 3⟩, ⟨0, 2, 438⟩, ⟨0, 3, 433⟩, ⟨1, 2, 449⟩, ⟨1, 3, 423⟩, ⟨2, 3, 335⟩], triples := #[] }
def er173_121 : Row := { vars := #[43, 188, 49], coeff := #[1, 1, 1], bound := 1, weight := 214536, edges := #[⟨0, 1, 141⟩, ⟨0, 2, 11⟩, ⟨1, 2, 161⟩], triples := #[] }
def er173_122 : Row := { vars := #[43, 189, 225], coeff := #[1, 1, 1], bound := 1, weight := 256324, edges := #[⟨0, 1, 139⟩, ⟨0, 2, 123⟩, ⟨1, 2, 33⟩], triples := #[] }
def er173_123 : Row := { vars := #[44, 166, 50], coeff := #[1, 1, 1], bound := 1, weight := 146611, edges := #[⟨0, 1, 171⟩, ⟨0, 2, 12⟩, ⟨1, 2, 179⟩], triples := #[] }
def er173_124 : Row := { vars := #[44, 55, 334, 357, 440, 376], coeff := #[1, 1, 1, 1, 1, 1], bound := 1, weight := 13226, edges := #[⟨0, 1, 4⟩, ⟨0, 2, 386⟩, ⟨0, 3, 509⟩, ⟨0, 4, 457⟩, ⟨0, 5, 487⟩, ⟨1, 2, 391⟩, ⟨1, 3, 499⟩, ⟨1, 4, 447⟩, ⟨1, 5, 477⟩, ⟨2, 3, 335⟩, ⟨2, 4, 283⟩, ⟨2, 5, 313⟩, ⟨3, 4, 196⟩, ⟨3, 5, 279⟩, ⟨4, 5, 237⟩], triples := #[] }
def er173_125 : Row := { vars := #[44, 224, 186], coeff := #[1, 1, 1], bound := 1, weight := 352241, edges := #[⟨0, 1, 122⟩, ⟨0, 2, 143⟩, ⟨1, 2, 29⟩], triples := #[] }
def er173_126 : Row := { vars := #[44, 253, 50], coeff := #[1, 1, 1], bound := 1, weight := 217782, edges := #[⟨0, 1, 111⟩, ⟨0, 2, 12⟩, ⟨1, 2, 119⟩], triples := #[] }
def er173_127 : Row := { vars := #[45, 391, 380], coeff := #[1, 1, 1], bound := 1, weight := 119367, edges := #[⟨0, 1, 477⟩, ⟨0, 2, 487⟩, ⟨1, 2, 275⟩], triples := #[] }
end HardyCapset20261020.Cert



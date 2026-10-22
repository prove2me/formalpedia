-- Prove2me | Definitions.Def_HardyCapsetEvaluationData010rows01V420261021
-- name    : HardyCapsetEvaluationData010rows01V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T01:25:34.752534+00:00
-- url     : https://prove2.me/theorems/899344f8-3984-4a56-8187-f160abbe2107
-- title:
--   HardyCapsetEvaluationData010rows01V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er010_064 : Row := { vars := #[24, 457, 78, 382], coeff := #[1, 1, 1, 1], bound := 1, weight := 652976, edges := #[⟨0, 1, 209⟩, ⟨0, 2, 157⟩, ⟨0, 3, 455⟩, ⟨1, 2, 313⟩, ⟨1, 3, 102⟩, ⟨2, 3, 379⟩], triples := #[] }
def er010_065 : Row := { vars := #[25, 450, 160, 246], coeff := #[1, 1, 1, 1], bound := 1, weight := 458361, edges := #[⟨0, 1, 220⟩, ⟨0, 2, 84⟩, ⟨0, 3, 380⟩, ⟨1, 2, 260⟩, ⟨1, 3, 4⟩, ⟨2, 3, 420⟩], triples := #[] }
def er010_066 : Row := { vars := #[25, 595, 320], coeff := #[1, 1, 1], bound := 1, weight := 541640, edges := #[⟨0, 1, 288⟩, ⟨0, 2, 511⟩, ⟨1, 2, 66⟩], triples := #[] }
def er010_067 : Row := { vars := #[26, 385, 536], coeff := #[1, 1, 1], bound := 1, weight := 210936, edges := #[⟨0, 1, 450⟩, ⟨0, 2, 337⟩, ⟨1, 2, 70⟩], triples := #[] }
def er010_068 : Row := { vars := #[26, 528, 343], coeff := #[1, 1, 1], bound := 1, weight := 264681, edges := #[⟨0, 1, 351⟩, ⟨0, 2, 435⟩, ⟨1, 2, 6⟩], triples := #[] }
def er010_069 : Row := { vars := #[26, 535, 380], coeff := #[1, 1, 1], bound := 1, weight := 292806, edges := #[⟨0, 1, 341⟩, ⟨0, 2, 454⟩, ⟨1, 2, 67⟩], triples := #[] }
def er010_070 : Row := { vars := #[26, 551, 94, 306], coeff := #[1, 1, 1, 1], bound := 1, weight := 40855, edges := #[⟨0, 1, 271⟩, ⟨0, 2, 139⟩, ⟨0, 3, 466⟩, ⟨1, 2, 240⟩, ⟨1, 3, 48⟩, ⟨2, 3, 424⟩], triples := #[] }
def er010_071 : Row := { vars := #[27, 536, 593], coeff := #[1, 1, 1], bound := 1, weight := 602511, edges := #[⟨0, 1, 336⟩, ⟨0, 2, 292⟩, ⟨1, 2, 403⟩], triples := #[] }
def er010_072 : Row := { vars := #[27, 41, 320, 524], coeff := #[1, 1, 1, 1], bound := 1, weight := 234411, edges := #[⟨0, 1, 45⟩, ⟨0, 2, 508⟩, ⟨0, 3, 348⟩, ⟨1, 2, 498⟩, ⟨1, 3, 338⟩, ⟨2, 3, 120⟩], triples := #[] }
def er010_073 : Row := { vars := #[28, 527, 242], coeff := #[1, 1, 1], bound := 1, weight := 200607, edges := #[⟨0, 1, 344⟩, ⟨0, 2, 381⟩, ⟨1, 2, 143⟩], triples := #[] }
def er010_074 : Row := { vars := #[28, 42, 520, 321], coeff := #[1, 1, 1, 1], bound := 1, weight := 485589, edges := #[⟨0, 1, 36⟩, ⟨0, 2, 349⟩, ⟨0, 3, 505⟩, ⟨1, 2, 339⟩, ⟨1, 3, 495⟩, ⟨2, 3, 123⟩], triples := #[] }
def er010_075 : Row := { vars := #[28, 446, 88, 246], coeff := #[1, 1, 1, 1], bound := 1, weight := 307436, edges := #[⟨0, 1, 221⟩, ⟨0, 2, 136⟩, ⟨0, 3, 377⟩, ⟨1, 2, 317⟩, ⟨1, 3, 12⟩, ⟨2, 3, 473⟩], triples := #[] }
def er010_076 : Row := { vars := #[28, 456, 78, 382], coeff := #[1, 1, 1, 1], bound := 1, weight := 6370, edges := #[⟨0, 1, 209⟩, ⟨0, 2, 154⟩, ⟨0, 3, 451⟩, ⟨1, 2, 317⟩, ⟨1, 3, 105⟩, ⟨2, 3, 379⟩], triples := #[] }
def er010_077 : Row := { vars := #[29, 43, 276, 484], coeff := #[1, 1, 1, 1], bound := 1, weight := 373018, edges := #[⟨0, 1, 37⟩, ⟨0, 2, 488⟩, ⟨0, 3, 324⟩, ⟨1, 2, 478⟩, ⟨1, 3, 314⟩, ⟨2, 3, 80⟩], triples := #[] }
def er010_078 : Row := { vars := #[29, 43, 580, 381], coeff := #[1, 1, 1, 1], bound := 1, weight := 6140, edges := #[⟨0, 1, 37⟩, ⟨0, 2, 295⟩, ⟨0, 3, 451⟩, ⟨1, 2, 285⟩, ⟨1, 3, 441⟩, ⟨2, 3, 183⟩], triples := #[] }
def er010_079 : Row := { vars := #[29, 43, 585, 376], coeff := #[1, 1, 1, 1], bound := 1, weight := 434758, edges := #[⟨0, 1, 37⟩, ⟨0, 2, 291⟩, ⟨0, 3, 455⟩, ⟨1, 2, 281⟩, ⟨1, 3, 445⟩, ⟨2, 3, 183⟩], triples := #[] }
def er010_080 : Row := { vars := #[29, 457, 150, 252], coeff := #[1, 1, 1, 1], bound := 1, weight := 186086, edges := #[⟨0, 1, 204⟩, ⟨0, 2, 94⟩, ⟨0, 3, 368⟩, ⟨1, 2, 260⟩, ⟨1, 3, 25⟩, ⟨2, 3, 424⟩], triples := #[] }
def er010_081 : Row := { vars := #[31, 534, 588], coeff := #[1, 1, 1], bound := 1, weight := 554612, edges := #[⟨0, 1, 340⟩, ⟨0, 2, 292⟩, ⟨1, 2, 403⟩], triples := #[] }
def er010_082 : Row := { vars := #[31, 279, 162, 565], coeff := #[1, 1, 1, 1], bound := 1, weight := 241998, edges := #[⟨0, 1, 489⟩, ⟨0, 2, 79⟩, ⟨0, 3, 252⟩, ⟨1, 2, 400⟩, ⟨1, 3, 48⟩, ⟨2, 3, 313⟩], triples := #[] }
def er010_083 : Row := { vars := #[31, 289, 594], coeff := #[1, 1, 1], bound := 1, weight := 128604, edges := #[⟨0, 1, 475⟩, ⟨0, 2, 286⟩, ⟨1, 2, 23⟩], triples := #[] }
def er010_084 : Row := { vars := #[32, 522, 385], coeff := #[1, 1, 1], bound := 1, weight := 275203, edges := #[⟨0, 1, 344⟩, ⟨0, 2, 456⟩, ⟨1, 2, 42⟩], triples := #[] }
def er010_085 : Row := { vars := #[32, 46, 548, 336], coeff := #[1, 1, 1, 1], bound := 1, weight := 114031, edges := #[⟨0, 1, 44⟩, ⟨0, 2, 273⟩, ⟨0, 3, 429⟩, ⟨1, 2, 263⟩, ⟨1, 3, 419⟩, ⟨2, 3, 132⟩], triples := #[] }
def er010_086 : Row := { vars := #[32, 46, 589, 375], coeff := #[1, 1, 1, 1], bound := 1, weight := 114031, edges := #[⟨0, 1, 44⟩, ⟨0, 2, 296⟩, ⟨0, 3, 452⟩, ⟨1, 2, 286⟩, ⟨1, 3, 442⟩, ⟨2, 3, 180⟩], triples := #[] }
def er010_087 : Row := { vars := #[32, 250, 591, 84], coeff := #[1, 1, 1, 1], bound := 1, weight := 81475, edges := #[⟨0, 1, 381⟩, ⟨0, 2, 295⟩, ⟨0, 3, 136⟩, ⟨1, 2, 85⟩, ⟨1, 3, 473⟩, ⟨2, 3, 207⟩], triples := #[] }
def er010_088 : Row := { vars := #[32, 252, 591, 82], coeff := #[1, 1, 1, 1], bound := 1, weight := 348792, edges := #[⟨0, 1, 365⟩, ⟨0, 2, 295⟩, ⟨0, 3, 157⟩, ⟨1, 2, 102⟩, ⟨1, 3, 473⟩, ⟨2, 3, 223⟩], triples := #[] }
def er010_089 : Row := { vars := #[33, 454, 156, 250], coeff := #[1, 1, 1, 1], bound := 1, weight := 60684, edges := #[⟨0, 1, 220⟩, ⟨0, 2, 76⟩, ⟨0, 3, 380⟩, ⟨1, 2, 260⟩, ⟨1, 3, 12⟩, ⟨2, 3, 420⟩], triples := #[] }
def er010_090 : Row := { vars := #[33, 458, 146, 254], coeff := #[1, 1, 1, 1], bound := 1, weight := 711014, edges := #[⟨0, 1, 208⟩, ⟨0, 2, 94⟩, ⟨0, 3, 368⟩, ⟨1, 2, 260⟩, ⟨1, 3, 25⟩, ⟨2, 3, 420⟩], triples := #[] }
def er010_091 : Row := { vars := #[35, 287, 158, 570], coeff := #[1, 1, 1, 1], bound := 1, weight := 257508, edges := #[⟨0, 1, 489⟩, ⟨0, 2, 79⟩, ⟨0, 3, 253⟩, ⟨1, 2, 399⟩, ⟨1, 3, 48⟩, ⟨2, 3, 313⟩], triples := #[] }
def er010_092 : Row := { vars := #[35, 45, 519, 325], coeff := #[1, 1, 1, 1], bound := 1, weight := 513435, edges := #[⟨0, 1, 45⟩, ⟨0, 2, 344⟩, ⟨0, 3, 508⟩, ⟨1, 2, 338⟩, ⟨1, 3, 502⟩, ⟨2, 3, 120⟩], triples := #[] }
def er010_093 : Row := { vars := #[35, 593, 315], coeff := #[1, 1, 1], bound := 1, weight := 7494, edges := #[⟨0, 1, 296⟩, ⟨0, 2, 504⟩, ⟨1, 2, 38⟩], triples := #[] }
def er010_094 : Row := { vars := #[35, 492, 366, 152], coeff := #[1, 1, 1, 1], bound := 1, weight := 221566, edges := #[⟨0, 1, 315⟩, ⟨0, 2, 413⟩, ⟨0, 3, 97⟩, ⟨1, 2, 68⟩, ⟨1, 3, 239⟩, ⟨2, 3, 487⟩], triples := #[] }
def er010_095 : Row := { vars := #[36, 30, 448, 244], coeff := #[1, 1, 1, 1], bound := 1, weight := 88455, edges := #[⟨0, 1, 44⟩, ⟨0, 2, 208⟩, ⟨0, 3, 368⟩, ⟨1, 2, 216⟩, ⟨1, 3, 376⟩, ⟨2, 3, 0⟩], triples := #[] }
def er010_096 : Row := { vars := #[36, 34, 548, 344], coeff := #[1, 1, 1, 1], bound := 1, weight := 671640, edges := #[⟨0, 1, 36⟩, ⟨0, 2, 262⟩, ⟨0, 3, 422⟩, ⟨1, 2, 272⟩, ⟨1, 3, 432⟩, ⟨2, 3, 140⟩], triples := #[] }
def er010_097 : Row := { vars := #[36, 556, 90, 352], coeff := #[1, 1, 1, 1], bound := 1, weight := 202659, edges := #[⟨0, 1, 275⟩, ⟨0, 2, 167⟩, ⟨0, 3, 435⟩, ⟨1, 2, 242⟩, ⟨1, 3, 162⟩, ⟨2, 3, 402⟩], triples := #[] }
def er010_098 : Row := { vars := #[37, 388, 335], coeff := #[1, 1, 1], bound := 1, weight := 627894, edges := #[⟨0, 1, 442⟩, ⟨0, 2, 506⟩, ⟨1, 2, 240⟩], triples := #[] }
def er010_099 : Row := { vars := #[37, 538, 587], coeff := #[1, 1, 1], bound := 1, weight := 263212, edges := #[⟨0, 1, 350⟩, ⟨0, 2, 286⟩, ⟨1, 2, 399⟩], triples := #[] }
def er010_100 : Row := { vars := #[38, 257, 92, 461], coeff := #[1, 1, 1, 1], bound := 1, weight := 61125, edges := #[⟨0, 1, 377⟩, ⟨0, 2, 164⟩, ⟨0, 3, 217⟩, ⟨1, 2, 487⟩, ⟨1, 3, 35⟩, ⟨2, 3, 327⟩], triples := #[] }
def er010_101 : Row := { vars := #[38, 539, 419], coeff := #[1, 1, 1], bound := 1, weight := 547900, edges := #[⟨0, 1, 344⟩, ⟨0, 2, 229⟩, ⟨1, 2, 477⟩], triples := #[] }
def er010_102 : Row := { vars := #[38, 461, 335], coeff := #[1, 1, 1], bound := 1, weight := 372107, edges := #[⟨0, 1, 217⟩, ⟨0, 2, 504⟩, ⟨1, 2, 166⟩], triples := #[] }
def er010_103 : Row := { vars := #[38, 334, 584], coeff := #[1, 1, 1], bound := 1, weight := 18870, edges := #[⟨0, 1, 508⟩, ⟨0, 2, 286⟩, ⟨1, 2, 57⟩], triples := #[] }
def er010_104 : Row := { vars := #[39, 410, 598], coeff := #[1, 1, 1], bound := 1, weight := 896787, edges := #[⟨0, 1, 230⟩, ⟨0, 2, 294⟩, ⟨1, 2, 420⟩], triples := #[] }
def er010_105 : Row := { vars := #[39, 598, 320], coeff := #[1, 1, 1], bound := 1, weight := 44922, edges := #[⟨0, 1, 294⟩, ⟨0, 2, 501⟩, ⟨1, 2, 56⟩], triples := #[] }
def er010_106 : Row := { vars := #[41, 282, 148, 482], coeff := #[1, 1, 1, 1], bound := 1, weight := 638305, edges := #[⟨0, 1, 475⟩, ⟨0, 2, 76⟩, ⟨0, 3, 319⟩, ⟨1, 2, 402⟩, ⟨1, 3, 82⟩, ⟨2, 3, 243⟩], triples := #[] }
def er010_107 : Row := { vars := #[41, 333, 383], coeff := #[1, 1, 1], bound := 1, weight := 19565, edges := #[⟨0, 1, 510⟩, ⟨0, 2, 442⟩, ⟨1, 2, 240⟩], triples := #[] }
def er010_108 : Row := { vars := #[41, 597, 320], coeff := #[1, 1, 1], bound := 1, weight := 75774, edges := #[⟨0, 1, 296⟩, ⟨0, 2, 498⟩, ⟨1, 2, 59⟩], triples := #[] }
def er010_109 : Row := { vars := #[42, 256, 84, 460], coeff := #[1, 1, 1, 1], bound := 1, weight := 301554, edges := #[⟨0, 1, 377⟩, ⟨0, 2, 167⟩, ⟨0, 3, 217⟩, ⟨1, 2, 487⟩, ⟨1, 3, 32⟩, ⟨2, 3, 327⟩], triples := #[] }
def er010_110 : Row := { vars := #[42, 319, 451], coeff := #[1, 1, 1], bound := 1, weight := 97222, edges := #[⟨0, 1, 502⟩, ⟨0, 2, 205⟩, ⟨1, 2, 146⟩], triples := #[] }
def er010_111 : Row := { vars := #[43, 384, 230], coeff := #[1, 1, 1], bound := 1, weight := 73240, edges := #[⟨0, 1, 444⟩, ⟨0, 2, 393⟩, ⟨1, 2, 264⟩], triples := #[] }
def er010_112 : Row := { vars := #[43, 438, 583], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 232⟩, ⟨0, 2, 288⟩, ⟨1, 2, 424⟩], triples := #[] }
def er010_113 : Row := { vars := #[43, 447, 150, 247], coeff := #[1, 1, 1, 1], bound := 1, weight := 9592, edges := #[⟨0, 1, 208⟩, ⟨0, 2, 79⟩, ⟨0, 3, 364⟩, ⟨1, 2, 274⟩, ⟨1, 3, 15⟩, ⟨2, 3, 430⟩], triples := #[] }
def er010_114 : Row := { vars := #[43, 597, 320], coeff := #[1, 1, 1], bound := 1, weight := 103255, edges := #[⟨0, 1, 294⟩, ⟨0, 2, 497⟩, ⟨1, 2, 59⟩], triples := #[] }
def er010_115 : Row := { vars := #[45, 293, 166, 495], coeff := #[1, 1, 1, 1], bound := 1, weight := 486566, edges := #[⟨0, 1, 489⟩, ⟨0, 2, 107⟩, ⟨0, 3, 325⟩, ⟨1, 2, 403⟩, ⟨1, 3, 102⟩, ⟨2, 3, 242⟩], triples := #[] }
def er010_116 : Row := { vars := #[46, 319, 239], coeff := #[1, 1, 1], bound := 1, weight := 333534, edges := #[⟨0, 1, 498⟩, ⟨0, 2, 393⟩, ⟨1, 2, 313⟩], triples := #[] }
def er010_117 : Row := { vars := #[47, 393, 461], coeff := #[1, 1, 1], bound := 1, weight := 160195, edges := #[⟨0, 1, 450⟩, ⟨0, 2, 220⟩, ⟨1, 2, 103⟩], triples := #[] }
def er010_118 : Row := { vars := #[47, 461, 164, 255], coeff := #[1, 1, 1, 1], bound := 1, weight := 19565, edges := #[⟨0, 1, 220⟩, ⟨0, 2, 107⟩, ⟨0, 3, 376⟩, ⟨1, 2, 274⟩, ⟨1, 3, 32⟩, ⟨2, 3, 430⟩], triples := #[] }
def er010_119 : Row := { vars := #[47, 599, 255], coeff := #[1, 1, 1], bound := 1, weight := 591939, edges := #[⟨0, 1, 294⟩, ⟨0, 2, 376⟩, ⟨1, 2, 103⟩], triples := #[] }
def er010_120 : Row := { vars := #[48, 531, 304, 70], coeff := #[1, 1, 1, 1], bound := 1, weight := 29073, edges := #[⟨0, 1, 270⟩, ⟨0, 2, 453⟩, ⟨0, 3, 72⟩, ⟨1, 2, 81⟩, ⟨1, 3, 264⟩, ⟨2, 3, 447⟩], triples := #[] }
def er010_121 : Row := { vars := #[48, 155, 350, 554], coeff := #[1, 1, 1, 1], bound := 1, weight := 236803, edges := #[⟨0, 1, 56⟩, ⟨0, 2, 367⟩, ⟨0, 3, 207⟩, ⟨1, 2, 499⟩, ⟨1, 3, 339⟩, ⟨2, 3, 155⟩], triples := #[] }
def er010_122 : Row := { vars := #[48, 546, 161, 322], coeff := #[1, 1, 1, 1], bound := 1, weight := 522673, edges := #[⟨0, 1, 223⟩, ⟨0, 2, 46⟩, ⟨0, 3, 434⟩, ⟨1, 2, 335⟩, ⟨1, 3, 7⟩, ⟨2, 3, 364⟩], triples := #[] }
def er010_123 : Row := { vars := #[48, 430, 511], coeff := #[1, 1, 1], bound := 1, weight := 206975, edges := #[⟨0, 1, 303⟩, ⟨0, 2, 290⟩, ⟨1, 2, 509⟩], triples := #[] }
def er010_124 : Row := { vars := #[49, 550, 328], coeff := #[1, 1, 1], bound := 1, weight := 175351, edges := #[⟨0, 1, 218⟩, ⟨0, 2, 428⟩, ⟨1, 2, 11⟩], triples := #[] }
def er010_125 : Row := { vars := #[49, 67, 449, 245], coeff := #[1, 1, 1, 1], bound := 1, weight := 316101, edges := #[⟨0, 1, 81⟩, ⟨0, 2, 351⟩, ⟨0, 3, 511⟩, ⟨1, 2, 337⟩, ⟨1, 3, 497⟩, ⟨2, 3, 1⟩], triples := #[] }
def er010_126 : Row := { vars := #[49, 332, 208], coeff := #[1, 1, 1], bound := 1, weight := 377236, edges := #[⟨0, 1, 422⟩, ⟨0, 2, 466⟩, ⟨1, 2, 329⟩], triples := #[] }
def er010_127 : Row := { vars := #[50, 514, 528], coeff := #[1, 1, 1], bound := 1, weight := 275203, edges := #[⟨0, 1, 286⟩, ⟨0, 2, 275⟩, ⟨1, 2, 412⟩], triples := #[] }
end HardyCapset20261020.Cert



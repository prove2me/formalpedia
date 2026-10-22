-- Prove2me | Definitions.Def_HardyCapsetEvaluationData173rows02V420261021
-- name    : HardyCapsetEvaluationData173rows02V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:07:55.267436+00:00
-- url     : https://prove2.me/theorems/3c765782-657b-438d-bad8-6efca4bcd819
-- title:
--   HardyCapsetEvaluationData173rows02V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er173_128 : Row := { vars := #[47, 401, 560], coeff := #[1, 1, 1], bound := 1, weight := 415156, edges := #[⟨0, 1, 468⟩, ⟨0, 2, 217⟩, ⟨1, 2, 156⟩], triples := #[] }
def er173_129 : Row := { vars := #[47, 62, 260], coeff := #[1, 1, 1], bound := 1, weight := 145610, edges := #[⟨0, 1, 12⟩, ⟨0, 2, 100⟩, ⟨1, 2, 90⟩], triples := #[] }
def er173_130 : Row := { vars := #[59, 631, 238], coeff := #[1, 1, 1], bound := 1, weight := 119367, edges := #[⟨0, 1, 306⟩, ⟨0, 2, 114⟩, ⟨1, 2, 209⟩], triples := #[] }
def er173_131 : Row := { vars := #[60, 447, 591], coeff := #[1, 1, 1], bound := 1, weight := 456621, edges := #[⟨0, 1, 436⟩, ⟨0, 2, 314⟩, ⟨1, 2, 71⟩], triples := #[] }
def er173_132 : Row := { vars := #[60, 341, 354], coeff := #[1, 1, 1], bound := 1, weight := 543380, edges := #[⟨0, 1, 369⟩, ⟨0, 2, 381⟩, ⟨1, 2, 240⟩], triples := #[] }
def er173_133 : Row := { vars := #[61, 654, 366], coeff := #[1, 1, 1], bound := 1, weight := 322638, edges := #[⟨0, 1, 259⟩, ⟨0, 2, 490⟩, ⟨1, 2, 71⟩], triples := #[] }
def er173_134 : Row := { vars := #[61, 174, 184], coeff := #[1, 1, 1], bound := 1, weight := 622586, edges := #[⟨0, 1, 151⟩, ⟨0, 2, 143⟩, ⟨1, 2, 130⟩], triples := #[] }
def er173_135 : Row := { vars := #[61, 576, 499], coeff := #[1, 1, 1], bound := 1, weight := 54777, edges := #[⟨0, 1, 337⟩, ⟨0, 2, 404⟩, ⟨1, 2, 34⟩], triples := #[] }
def er173_136 : Row := { vars := #[62, 653, 366], coeff := #[1, 1, 1], bound := 1, weight := 122059, edges := #[⟨0, 1, 260⟩, ⟨0, 2, 491⟩, ⟨1, 2, 70⟩], triples := #[] }
def er173_137 : Row := { vars := #[62, 179, 260], coeff := #[1, 1, 1], bound := 1, weight := 293098, edges := #[⟨0, 1, 138⟩, ⟨0, 2, 90⟩, ⟨1, 2, 70⟩], triples := #[] }
def er173_138 : Row := { vars := #[63, 319, 339, 94], coeff := #[1, 1, 1, 1], bound := 1, weight := 73212, edges := #[⟨0, 1, 353⟩, ⟨0, 2, 396⟩, ⟨0, 3, 54⟩, ⟨1, 2, 196⟩, ⟨1, 3, 361⟩, ⟨2, 3, 398⟩], triples := #[] }
def er173_139 : Row := { vars := #[63, 319, 339, 79], coeff := #[1, 1, 1, 1], bound := 1, weight := 240054, edges := #[⟨0, 1, 353⟩, ⟨0, 2, 396⟩, ⟨0, 3, 64⟩, ⟨1, 2, 196⟩, ⟨1, 3, 373⟩, ⟨2, 3, 401⟩], triples := #[] }
def er173_140 : Row := { vars := #[63, 94, 451, 399], coeff := #[1, 1, 1, 1], bound := 1, weight := 686736, edges := #[⟨0, 1, 54⟩, ⟨0, 2, 426⟩, ⟨0, 3, 464⟩, ⟨1, 2, 432⟩, ⟨1, 3, 467⟩, ⟨2, 3, 242⟩], triples := #[] }
def er173_141 : Row := { vars := #[64, 319, 377, 80], coeff := #[1, 1, 1, 1], bound := 1, weight := 541786, edges := #[⟨0, 1, 352⟩, ⟨0, 2, 460⟩, ⟨0, 3, 65⟩, ⟨1, 2, 311⟩, ⟨1, 3, 372⟩, ⟨2, 3, 465⟩], triples := #[] }
def er173_142 : Row := { vars := #[64, 337, 480, 370], coeff := #[1, 1, 1, 1], bound := 1, weight := 119502, edges := #[⟨0, 1, 395⟩, ⟨0, 2, 410⟩, ⟨0, 3, 480⟩, ⟨1, 2, 250⟩, ⟨1, 3, 320⟩, ⟨2, 3, 242⟩], triples := #[] }
def er173_143 : Row := { vars := #[64, 337, 417, 364], coeff := #[1, 1, 1, 1], bound := 1, weight := 44228, edges := #[⟨0, 1, 395⟩, ⟨0, 2, 509⟩, ⟨0, 3, 488⟩, ⟨1, 2, 349⟩, ⟨1, 3, 328⟩, ⟨2, 3, 260⟩], triples := #[] }
def er173_144 : Row := { vars := #[64, 95, 240], coeff := #[1, 1, 1], bound := 1, weight := 294486, edges := #[⟨0, 1, 55⟩, ⟨0, 2, 84⟩, ⟨1, 2, 97⟩], triples := #[] }
def er173_145 : Row := { vars := #[65, 281, 297, 153], coeff := #[1, 1, 1, 1], bound := 1, weight := 211837, edges := #[⟨0, 1, 384⟩, ⟨0, 2, 393⟩, ⟨0, 3, 136⟩, ⟨1, 2, 218⟩, ⟨1, 3, 492⟩, ⟨2, 3, 509⟩], triples := #[] }
def er173_146 : Row := { vars := #[65, 170, 490], coeff := #[1, 1, 1], bound := 1, weight := 137899, edges := #[⟨0, 1, 150⟩, ⟨0, 2, 437⟩, ⟨1, 2, 370⟩], triples := #[] }
def er173_147 : Row := { vars := #[66, 133, 148], coeff := #[1, 1, 1], bound := 1, weight := 216630, edges := #[⟨0, 1, 178⟩, ⟨0, 2, 174⟩, ⟨1, 2, 84⟩], triples := #[] }
def er173_148 : Row := { vars := #[66, 279, 492], coeff := #[1, 1, 1], bound := 1, weight := 473948, edges := #[⟨0, 1, 126⟩, ⟨0, 2, 436⟩, ⟨1, 2, 502⟩], triples := #[] }
def er173_149 : Row := { vars := #[66, 409, 90], coeff := #[1, 1, 1], bound := 1, weight := 309424, edges := #[⟨0, 1, 491⟩, ⟨0, 2, 64⟩, ⟨1, 2, 509⟩], triples := #[] }
def er173_150 : Row := { vars := #[67, 412, 424, 551], coeff := #[1, 1, 1, 1], bound := 1, weight := 659374, edges := #[⟨0, 1, 508⟩, ⟨0, 2, 502⟩, ⟨0, 3, 217⟩, ⟨1, 2, 278⟩, ⟨1, 3, 156⟩, ⟨2, 3, 143⟩], triples := #[] }
def er173_151 : Row := { vars := #[67, 69, 551, 331, 323, 68], coeff := #[1, 1, 1, 1, 1, 1], bound := 1, weight := 340627, edges := #[⟨0, 1, 42⟩, ⟨0, 2, 217⟩, ⟨0, 3, 369⟩, ⟨0, 4, 381⟩, ⟨0, 5, 43⟩, ⟨1, 2, 219⟩, ⟨1, 3, 371⟩, ⟨1, 4, 383⟩, ⟨1, 5, 41⟩, ⟨2, 3, 12⟩, ⟨2, 4, 25⟩, ⟨2, 5, 216⟩, ⟨3, 4, 226⟩, ⟨3, 5, 368⟩, ⟨4, 5, 380⟩], triples := #[] }
def er173_152 : Row := { vars := #[68, 494, 586, 504], coeff := #[1, 1, 1, 1], bound := 1, weight := 659374, edges := #[⟨0, 1, 456⟩, ⟨0, 2, 315⟩, ⟨0, 3, 446⟩, ⟨1, 2, 10⟩, ⟨1, 3, 332⟩, ⟨2, 3, 33⟩], triples := #[] }
def er173_153 : Row := { vars := #[69, 150, 241, 152], coeff := #[1, 1, 1, 1], bound := 1, weight := 249050, edges := #[⟨0, 1, 144⟩, ⟨0, 2, 79⟩, ⟨0, 3, 136⟩, ⟨1, 2, 12⟩, ⟨1, 3, 111⟩, ⟨2, 3, 4⟩], triples := #[] }
def er173_154 : Row := { vars := #[69, 154, 566, 241, 342, 350], coeff := #[1, 1, 1, 1, 1, 1], bound := 1, weight := 410325, edges := #[⟨0, 1, 139⟩, ⟨0, 2, 242⟩, ⟨0, 3, 79⟩, ⟨0, 4, 403⟩, ⟨0, 5, 400⟩, ⟨1, 2, 306⟩, ⟨1, 3, 7⟩, ⟨1, 4, 467⟩, ⟨1, 5, 464⟩, ⟨2, 3, 252⟩, ⟨2, 4, 61⟩, ⟨2, 5, 48⟩, ⟨3, 4, 413⟩, ⟨3, 5, 410⟩, ⟨4, 5, 236⟩], triples := #[] }
def er173_155 : Row := { vars := #[70, 514, 620], coeff := #[1, 1, 1], bound := 1, weight := 31491, edges := #[⟨0, 1, 440⟩, ⟨0, 2, 344⟩, ⟨1, 2, 44⟩], triples := #[] }
def er173_156 : Row := { vars := #[70, 155, 124], coeff := #[1, 1, 1], bound := 1, weight := 136572, edges := #[⟨0, 1, 144⟩, ⟨0, 2, 179⟩, ⟨1, 2, 130⟩], triples := #[] }
def er173_157 : Row := { vars := #[70, 433, 550], coeff := #[1, 1, 1], bound := 1, weight := 535432, edges := #[⟨0, 1, 494⟩, ⟨0, 2, 217⟩, ⟨1, 2, 141⟩], triples := #[] }
def er173_158 : Row := { vars := #[70, 442, 72, 243], coeff := #[1, 1, 1, 1], bound := 1, weight := 296506, edges := #[⟨0, 1, 431⟩, ⟨0, 2, 47⟩, ⟨0, 3, 82⟩, ⟨1, 2, 430⟩, ⟨1, 3, 505⟩, ⟨2, 3, 84⟩], triples := #[] }
def er173_159 : Row := { vars := #[71, 156, 513], coeff := #[1, 1, 1], bound := 1, weight := 492226, edges := #[⟨0, 1, 142⟩, ⟨0, 2, 440⟩, ⟨1, 2, 363⟩], triples := #[] }
def er173_160 : Row := { vars := #[71, 418, 694], coeff := #[1, 1, 1], bound := 1, weight := 167149, edges := #[⟨0, 1, 503⟩, ⟨0, 2, 282⟩, ⟨1, 2, 45⟩], triples := #[] }
def er173_161 : Row := { vars := #[71, 242, 118], coeff := #[1, 1, 1], bound := 1, weight := 340627, edges := #[⟨0, 1, 84⟩, ⟨0, 2, 170⟩, ⟨1, 2, 45⟩], triples := #[] }
def er173_162 : Row := { vars := #[72, 141, 353], coeff := #[1, 1, 1], bound := 1, weight := 466516, edges := #[⟨0, 1, 175⟩, ⟨0, 2, 400⟩, ⟨1, 2, 481⟩], triples := #[] }
def er173_163 : Row := { vars := #[72, 73, 243], coeff := #[1, 1, 1], bound := 1, weight := 236979, edges := #[⟨0, 1, 45⟩, ⟨0, 2, 84⟩, ⟨1, 2, 80⟩], triples := #[] }
def er173_164 : Row := { vars := #[73, 269, 611], coeff := #[1, 1, 1], bound := 1, weight := 349735, edges := #[⟨0, 1, 131⟩, ⟨0, 2, 304⟩, ⟨1, 2, 197⟩], triples := #[] }
def er173_165 : Row := { vars := #[73, 102, 88], coeff := #[1, 1, 1], bound := 1, weight := 193979, edges := #[⟨0, 1, 60⟩, ⟨0, 2, 69⟩, ⟨1, 2, 47⟩], triples := #[] }
def er173_166 : Row := { vars := #[74, 277, 583], coeff := #[1, 1, 1], bound := 1, weight := 509913, edges := #[⟨0, 1, 127⟩, ⟨0, 2, 328⟩, ⟨1, 2, 227⟩], triples := #[] }
def er173_167 : Row := { vars := #[74, 674, 182], coeff := #[1, 1, 1], bound := 1, weight := 89692, edges := #[⟨0, 1, 250⟩, ⟨0, 2, 191⟩, ⟨1, 2, 196⟩], triples := #[] }
def er173_168 : Row := { vars := #[74, 170, 89], coeff := #[1, 1, 1], bound := 1, weight := 400397, edges := #[⟨0, 1, 157⟩, ⟨0, 2, 70⟩, ⟨1, 2, 144⟩], triples := #[] }
def er173_169 : Row := { vars := #[75, 645, 168], coeff := #[1, 1, 1], bound := 1, weight := 377415, edges := #[⟨0, 1, 274⟩, ⟨0, 2, 150⟩, ⟨1, 2, 237⟩], triples := #[] }
def er173_170 : Row := { vars := #[75, 155, 202], coeff := #[1, 1, 1], bound := 1, weight := 258087, edges := #[⟨0, 1, 141⟩, ⟨0, 2, 110⟩, ⟨1, 2, 48⟩], triples := #[] }
def er173_171 : Row := { vars := #[75, 691, 628], coeff := #[1, 1, 1], bound := 1, weight := 364499, edges := #[⟨0, 1, 297⟩, ⟨0, 2, 350⟩, ⟨1, 2, 400⟩], triples := #[] }
def er173_172 : Row := { vars := #[76, 331, 122], coeff := #[1, 1, 1], bound := 1, weight := 505117, edges := #[⟨0, 1, 353⟩, ⟨0, 2, 175⟩, ⟨1, 2, 490⟩], triples := #[] }
def er173_173 : Row := { vars := #[76, 462, 416], coeff := #[1, 1, 1], bound := 1, weight := 16788, edges := #[⟨0, 1, 408⟩, ⟨0, 2, 502⟩, ⟨1, 2, 211⟩], triples := #[] }
def er173_174 : Row := { vars := #[76, 81, 256], coeff := #[1, 1, 1], bound := 1, weight := 49167, edges := #[⟨0, 1, 59⟩, ⟨0, 2, 83⟩, ⟨1, 2, 75⟩], triples := #[] }
def er173_175 : Row := { vars := #[76, 102, 327, 246], coeff := #[1, 1, 1, 1], bound := 1, weight := 311595, edges := #[⟨0, 1, 42⟩, ⟨0, 2, 370⟩, ⟨0, 3, 90⟩, ⟨1, 2, 352⟩, ⟨1, 3, 75⟩, ⟨2, 3, 425⟩], triples := #[] }
def er173_176 : Row := { vars := #[77, 393, 381], coeff := #[1, 1, 1], bound := 1, weight := 633338, edges := #[⟨0, 1, 460⟩, ⟨0, 2, 462⟩, ⟨1, 2, 256⟩], triples := #[] }
def er173_177 : Row := { vars := #[77, 159, 167], coeff := #[1, 1, 1], bound := 1, weight := 95372, edges := #[⟨0, 1, 150⟩, ⟨0, 2, 144⟩, ⟨1, 2, 110⟩], triples := #[] }
def er173_178 : Row := { vars := #[77, 159, 331], coeff := #[1, 1, 1], bound := 1, weight := 154258, edges := #[⟨0, 1, 150⟩, ⟨0, 2, 352⟩, ⟨1, 2, 469⟩], triples := #[] }
def er173_179 : Row := { vars := #[77, 82, 169], coeff := #[1, 1, 1], bound := 1, weight := 117034, edges := #[⟨0, 1, 60⟩, ⟨0, 2, 143⟩, ⟨1, 2, 135⟩], triples := #[] }
def er173_180 : Row := { vars := #[78, 101, 245], coeff := #[1, 1, 1], bound := 1, weight := 221042, edges := #[⟨0, 1, 48⟩, ⟨0, 2, 91⟩, ⟨1, 2, 81⟩], triples := #[] }
def er173_181 : Row := { vars := #[78, 350, 245], coeff := #[1, 1, 1], bound := 1, weight := 519548, edges := #[⟨0, 1, 396⟩, ⟨0, 2, 91⟩, ⟨1, 2, 405⟩], triples := #[] }
def er173_182 : Row := { vars := #[79, 394, 167], coeff := #[1, 1, 1], bound := 1, weight := 759947, edges := #[⟨0, 1, 458⟩, ⟨0, 2, 140⟩, ⟨1, 2, 433⟩], triples := #[] }
def er173_183 : Row := { vars := #[80, 393, 324], coeff := #[1, 1, 1], bound := 1, weight := 52024, edges := #[⟨0, 1, 459⟩, ⟨0, 2, 362⟩, ⟨1, 2, 311⟩], triples := #[] }
def er173_184 : Row := { vars := #[80, 157, 554, 497], coeff := #[1, 1, 1, 1], bound := 1, weight := 152371, edges := #[⟨0, 1, 151⟩, ⟨0, 2, 194⟩, ⟨0, 3, 445⟩, ⟨1, 2, 311⟩, ⟨1, 3, 371⟩, ⟨2, 3, 84⟩], triples := #[] }
def er173_185 : Row := { vars := #[81, 163, 678], coeff := #[1, 1, 1], bound := 1, weight := 119367, edges := #[⟨0, 1, 150⟩, ⟨0, 2, 297⟩, ⟨1, 2, 217⟩], triples := #[] }
def er173_186 : Row := { vars := #[81, 440, 99, 367], coeff := #[1, 1, 1, 1], bound := 1, weight := 695590, edges := #[⟨0, 1, 432⟩, ⟨0, 2, 38⟩, ⟨0, 3, 472⟩, ⟨1, 2, 426⟩, ⟨1, 3, 218⟩, ⟨2, 3, 470⟩], triples := #[] }
def er173_187 : Row := { vars := #[82, 157, 100], coeff := #[1, 1, 1], bound := 1, weight := 219968, edges := #[⟨0, 1, 155⟩, ⟨0, 2, 39⟩, ⟨1, 2, 142⟩], triples := #[] }
def er173_188 : Row := { vars := #[82, 200, 484], coeff := #[1, 1, 1], bound := 1, weight := 349735, edges := #[⟨0, 1, 118⟩, ⟨0, 2, 405⟩, ⟨1, 2, 502⟩], triples := #[] }
def er173_189 : Row := { vars := #[82, 329, 489, 100], coeff := #[1, 1, 1, 1], bound := 1, weight := 313265, edges := #[⟨0, 1, 360⟩, ⟨0, 2, 454⟩, ⟨0, 3, 39⟩, ⟨1, 2, 252⟩, ⟨1, 3, 352⟩, ⟨2, 3, 448⟩], triples := #[] }
def er173_190 : Row := { vars := #[83, 265, 178], coeff := #[1, 1, 1], bound := 1, weight := 37511, edges := #[⟨0, 1, 131⟩, ⟨0, 2, 191⟩, ⟨1, 2, 48⟩], triples := #[] }
def er173_191 : Row := { vars := #[83, 575, 614, 639], coeff := #[1, 1, 1, 1], bound := 1, weight := 237060, edges := #[⟨0, 1, 329⟩, ⟨0, 2, 350⟩, ⟨0, 3, 274⟩, ⟨1, 2, 416⟩, ⟨1, 3, 354⟩, ⟨2, 3, 386⟩], triples := #[] }
end HardyCapset20261020.Cert



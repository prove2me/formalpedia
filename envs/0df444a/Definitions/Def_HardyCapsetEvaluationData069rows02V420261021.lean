-- Prove2me | Definitions.Def_HardyCapsetEvaluationData069rows02V420261021
-- name    : HardyCapsetEvaluationData069rows02V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:43:23.778185+00:00
-- url     : https://prove2.me/theorems/33ba27f1-a0ef-4891-bef5-681f11114138
-- title:
--   HardyCapsetEvaluationData069rows02V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er069_128 : Row := { vars := #[313, 335], coeff := #[1, 1], bound := 1, weight := 109757, edges := #[⟨0, 1, 373⟩], triples := #[] }
def er069_129 : Row := { vars := #[325, 423], coeff := #[1, 1], bound := 1, weight := 451220, edges := #[⟨0, 1, 410⟩], triples := #[] }
def er069_130 : Row := { vars := #[326, 437], coeff := #[1, 1], bound := 1, weight := 170732, edges := #[⟨0, 1, 457⟩], triples := #[] }
def er069_131 : Row := { vars := #[327, 428], coeff := #[1, 1], bound := 1, weight := 560976, edges := #[⟨0, 1, 439⟩], triples := #[] }
def er069_132 : Row := { vars := #[349, 350], coeff := #[1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 413⟩], triples := #[] }
def er069_133 : Row := { vars := #[355, 435], coeff := #[1, 1], bound := 1, weight := 335366, edges := #[⟨0, 1, 372⟩], triples := #[] }
def er069_134 : Row := { vars := #[359, 439], coeff := #[1, 1], bound := 1, weight := 500001, edges := #[⟨0, 1, 356⟩], triples := #[] }
def er069_135 : Row := { vars := #[378, 385], coeff := #[1, 1], bound := 1, weight := 835366, edges := #[⟨0, 1, 457⟩], triples := #[] }
def er069_136 : Row := { vars := #[381, 384], coeff := #[1, 1], bound := 1, weight := 274391, edges := #[⟨0, 1, 446⟩], triples := #[] }
def er069_137 : Row := { vars := #[388, 407], coeff := #[1, 1], bound := 1, weight := 176830, edges := #[⟨0, 1, 361⟩], triples := #[] }
def er069_138 : Row := { vars := #[389, 392], coeff := #[1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 457⟩], triples := #[] }
def er069_139 : Row := { vars := #[393, 400], coeff := #[1, 1], bound := 1, weight := 603659, edges := #[⟨0, 1, 467⟩], triples := #[] }
def er069_140 : Row := { vars := #[401, 411], coeff := #[1, 1], bound := 1, weight := 286586, edges := #[⟨0, 1, 493⟩], triples := #[] }
def er069_141 : Row := { vars := #[428, 443], coeff := #[1, 1], bound := 1, weight := 225610, edges := #[⟨0, 1, 501⟩], triples := #[] }
def er069_142 : Row := { vars := #[1, 243, 315], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 436⟩, ⟨0, 2, 224⟩, ⟨1, 2, 120⟩], triples := #[] }
def er069_143 : Row := { vars := #[3, 6, 85], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 27⟩, ⟨0, 2, 148⟩, ⟨1, 2, 135⟩], triples := #[] }
def er069_144 : Row := { vars := #[5, 333, 263], coeff := #[1, 1, 1], bound := 1, weight := 274391, edges := #[⟨0, 1, 218⟩, ⟨0, 2, 424⟩, ⟨1, 2, 98⟩], triples := #[] }
def er069_145 : Row := { vars := #[5, 184, 415], coeff := #[1, 1, 1], bound := 1, weight := 725610, edges := #[⟨0, 1, 366⟩, ⟨0, 2, 264⟩, ⟨1, 2, 90⟩], triples := #[] }
def er069_146 : Row := { vars := #[7, 335, 79], coeff := #[1, 1, 1], bound := 1, weight := 890244, edges := #[⟨0, 1, 208⟩, ⟨0, 2, 153⟩, ⟨1, 2, 341⟩], triples := #[] }
def er069_147 : Row := { vars := #[8, 321, 169], coeff := #[1, 1, 1], bound := 1, weight := 890244, edges := #[⟨0, 1, 228⟩, ⟨0, 2, 388⟩, ⟨1, 2, 22⟩], triples := #[] }
def er069_148 : Row := { vars := #[9, 334, 272], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 206⟩, ⟨0, 2, 434⟩, ⟨1, 2, 90⟩], triples := #[] }
def er069_149 : Row := { vars := #[10, 418, 205], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 255⟩, ⟨0, 2, 475⟩, ⟨1, 2, 28⟩], triples := #[] }
def er069_150 : Row := { vars := #[11, 256, 241], coeff := #[1, 1, 1], bound := 1, weight := 6098, edges := #[⟨0, 1, 426⟩, ⟨0, 2, 445⟩, ⟨1, 2, 332⟩], triples := #[] }
def er069_151 : Row := { vars := #[11, 267, 241], coeff := #[1, 1, 1], bound := 1, weight := 713415, edges := #[⟨0, 1, 432⟩, ⟨0, 2, 445⟩, ⟨1, 2, 334⟩], triples := #[] }
def er069_152 : Row := { vars := #[17, 33, 68, 73], coeff := #[1, 1, 1, 1], bound := 1, weight := 274391, edges := #[⟨0, 1, 36⟩, ⟨0, 2, 154⟩, ⟨0, 3, 136⟩, ⟨1, 2, 147⟩, ⟨1, 3, 167⟩, ⟨2, 3, 110⟩], triples := #[] }
def er069_153 : Row := { vars := #[17, 61, 121], coeff := #[1, 1, 1], bound := 1, weight := 725610, edges := #[⟨0, 1, 168⟩, ⟨0, 2, 94⟩, ⟨1, 2, 51⟩], triples := #[] }
def er069_154 : Row := { vars := #[18, 441, 114], coeff := #[1, 1, 1], bound := 1, weight := 676830, edges := #[⟨0, 1, 276⟩, ⟨0, 2, 108⟩, ⟨1, 2, 325⟩], triples := #[] }
def er069_155 : Row := { vars := #[20, 308, 320], coeff := #[1, 1, 1], bound := 1, weight := 664635, edges := #[⟨0, 1, 224⟩, ⟨0, 2, 219⟩, ⟨1, 2, 399⟩], triples := #[] }
def er069_156 : Row := { vars := #[22, 321, 169], coeff := #[1, 1, 1], bound := 1, weight := 109757, edges := #[⟨0, 1, 201⟩, ⟨0, 2, 361⟩, ⟨1, 2, 22⟩], triples := #[] }
def er069_157 : Row := { vars := #[24, 239, 380, 189], coeff := #[1, 1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 490⟩, ⟨0, 2, 349⟩, ⟨0, 3, 485⟩, ⟨1, 2, 124⟩, ⟨1, 3, 264⟩, ⟨2, 3, 109⟩], triples := #[] }
def er069_158 : Row := { vars := #[24, 28, 126], coeff := #[1, 1, 1], bound := 1, weight := 500001, edges := #[⟨0, 1, 36⟩, ⟨0, 2, 84⟩, ⟨1, 2, 104⟩], triples := #[] }
def er069_159 : Row := { vars := #[25, 34, 280, 393, 427], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 396342, edges := #[⟨0, 1, 45⟩, ⟨0, 2, 455⟩, ⟨0, 3, 271⟩, ⟨0, 4, 291⟩, ⟨1, 2, 445⟩, ⟨1, 3, 261⟩, ⟨1, 4, 281⟩, ⟨2, 3, 169⟩, ⟨2, 4, 181⟩, ⟨3, 4, 469⟩], triples := #[] }
def er069_160 : Row := { vars := #[25, 292, 432, 241], coeff := #[1, 1, 1, 1], bound := 1, weight := 280488, edges := #[⟨0, 1, 436⟩, ⟨0, 2, 295⟩, ⟨0, 3, 431⟩, ⟨1, 2, 184⟩, ⟨1, 3, 317⟩, ⟨2, 3, 169⟩], triples := #[] }
def er069_161 : Row := { vars := #[25, 114, 386], coeff := #[1, 1, 1], bound := 1, weight := 323171, edges := #[⟨0, 1, 110⟩, ⟨0, 2, 334⟩, ⟨1, 2, 227⟩], triples := #[] }
def er069_162 : Row := { vars := #[29, 227, 379], coeff := #[1, 1, 1], bound := 1, weight := 109757, edges := #[⟨0, 1, 501⟩, ⟨0, 2, 341⟩, ⟨1, 2, 120⟩], triples := #[] }
def er069_163 : Row := { vars := #[30, 443, 182], coeff := #[1, 1, 1], bound := 1, weight := 774391, edges := #[⟨0, 1, 297⟩, ⟨0, 2, 399⟩, ⟨1, 2, 126⟩], triples := #[] }
def er069_164 : Row := { vars := #[31, 322, 170], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 213⟩, ⟨0, 2, 373⟩, ⟨1, 2, 32⟩], triples := #[] }
def er069_165 : Row := { vars := #[33, 384, 228, 341], coeff := #[1, 1, 1, 1], bound := 1, weight := 725610, edges := #[⟨0, 1, 330⟩, ⟨0, 2, 499⟩, ⟨0, 3, 315⟩, ⟨1, 2, 130⟩, ⟨1, 3, 434⟩, ⟨2, 3, 109⟩], triples := #[] }
def er069_166 : Row := { vars := #[40, 120, 74, 125], coeff := #[1, 1, 1, 1], bound := 1, weight := 396342, edges := #[⟨0, 1, 58⟩, ⟨0, 2, 121⟩, ⟨0, 3, 40⟩, ⟨1, 2, 13⟩, ⟨1, 3, 170⟩, ⟨2, 3, 33⟩], triples := #[] }
def er069_167 : Row := { vars := #[42, 178, 357], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 486⟩, ⟨0, 2, 294⟩, ⟨1, 2, 132⟩], triples := #[] }
def er069_168 : Row := { vars := #[44, 133, 353, 300], coeff := #[1, 1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 22⟩, ⟨0, 2, 295⟩, ⟨0, 3, 304⟩, ⟨1, 2, 223⟩, ⟨1, 3, 264⟩, ⟨2, 3, 503⟩], triples := #[] }
def er069_169 : Row := { vars := #[44, 138, 353, 296], coeff := #[1, 1, 1, 1], bound := 1, weight := 500001, edges := #[⟨0, 1, 4⟩, ⟨0, 2, 295⟩, ⟨0, 3, 307⟩, ⟨1, 2, 211⟩, ⟨1, 3, 264⟩, ⟨2, 3, 493⟩], triples := #[] }
def er069_170 : Row := { vars := #[44, 208, 211], coeff := #[1, 1, 1], bound := 1, weight := 500001, edges := #[⟨0, 1, 445⟩, ⟨0, 2, 441⟩, ⟨1, 2, 263⟩], triples := #[] }
def er069_171 : Row := { vars := #[45, 131, 207, 278], coeff := #[1, 1, 1, 1], bound := 1, weight := 451220, edges := #[⟨0, 1, 22⟩, ⟨0, 2, 447⟩, ⟨0, 3, 393⟩, ⟨1, 2, 368⟩, ⟨1, 3, 509⟩, ⟨2, 3, 212⟩], triples := #[] }
def er069_172 : Row := { vars := #[45, 139, 204, 278], coeff := #[1, 1, 1, 1], bound := 1, weight := 274391, edges := #[⟨0, 1, 7⟩, ⟨0, 2, 457⟩, ⟨0, 3, 393⟩, ⟨1, 2, 368⟩, ⟨1, 3, 499⟩, ⟨2, 3, 192⟩], triples := #[] }
def er069_173 : Row := { vars := #[49, 134, 136], coeff := #[1, 1, 1], bound := 1, weight := 170732, edges := #[⟨0, 1, 24⟩, ⟨0, 2, 6⟩, ⟨1, 2, 181⟩], triples := #[] }
def er069_174 : Row := { vars := #[49, 134, 444], coeff := #[1, 1, 1], bound := 1, weight := 829269, edges := #[⟨0, 1, 24⟩, ⟨0, 2, 227⟩, ⟨1, 2, 330⟩], triples := #[] }
def er069_175 : Row := { vars := #[50, 60, 394, 405, 246], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 81⟩, ⟨0, 2, 219⟩, ⟨0, 3, 242⟩, ⟨0, 4, 383⟩, ⟨1, 2, 207⟩, ⟨1, 3, 239⟩, ⟨1, 4, 371⟩, ⟨2, 3, 490⟩, ⟨2, 4, 133⟩, ⟨3, 4, 180⟩], triples := #[] }
def er069_176 : Row := { vars := #[51, 187, 402], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 485⟩, ⟨0, 2, 221⟩, ⟨1, 2, 119⟩], triples := #[] }
def er069_177 : Row := { vars := #[52, 121, 383], coeff := #[1, 1, 1], bound := 1, weight := 274391, edges := #[⟨0, 1, 37⟩, ⟨0, 2, 255⟩, ⟨1, 2, 206⟩], triples := #[] }
def er069_178 : Row := { vars := #[55, 287, 342], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 393⟩, ⟨0, 2, 250⟩, ⟨1, 2, 19⟩], triples := #[] }
def er069_179 : Row := { vars := #[56, 367, 429], coeff := #[1, 1, 1], bound := 1, weight := 170732, edges := #[⟨0, 1, 296⟩, ⟨0, 2, 230⟩, ⟨1, 2, 361⟩], triples := #[] }
def er069_180 : Row := { vars := #[57, 138, 58], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 32⟩, ⟨0, 2, 98⟩, ⟨1, 2, 28⟩], triples := #[] }
def er069_181 : Row := { vars := #[57, 171, 369], coeff := #[1, 1, 1], bound := 1, weight := 500001, edges := #[⟨0, 1, 477⟩, ⟨0, 2, 295⟩, ⟨1, 2, 148⟩], triples := #[] }
def er069_182 : Row := { vars := #[59, 268, 117], coeff := #[1, 1, 1], bound := 1, weight := 109757, edges := #[⟨0, 1, 402⟩, ⟨0, 2, 36⟩, ⟨1, 2, 469⟩], triples := #[] }
def er069_183 : Row := { vars := #[59, 285, 140], coeff := #[1, 1, 1], bound := 1, weight := 170732, edges := #[⟨0, 1, 386⟩, ⟨0, 2, 34⟩, ⟨1, 2, 490⟩], triples := #[] }
def er069_184 : Row := { vars := #[59, 292, 68], coeff := #[1, 1, 1], bound := 1, weight := 719513, edges := #[⟨0, 1, 391⟩, ⟨0, 2, 123⟩, ⟨1, 2, 357⟩], triples := #[] }
def er069_185 : Row := { vars := #[60, 234, 253, 398], coeff := #[1, 1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 415⟩, ⟨0, 2, 399⟩, ⟨0, 3, 211⟩, ⟨1, 2, 220⟩, ⟨1, 3, 26⟩, ⟨2, 3, 180⟩], triples := #[] }
def er069_186 : Row := { vars := #[65, 426, 98, 108], coeff := #[1, 1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 224⟩, ⟨0, 2, 57⟩, ⟨0, 3, 39⟩, ⟨1, 2, 333⟩, ⟨1, 3, 343⟩, ⟨2, 3, 132⟩], triples := #[] }
def er069_187 : Row := { vars := #[66, 360, 83], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 261⟩, ⟨0, 2, 73⟩, ⟨1, 2, 244⟩], triples := #[] }
def er069_188 : Row := { vars := #[67, 101, 291], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 61⟩, ⟨0, 2, 356⟩, ⟨1, 2, 469⟩], triples := #[] }
def er069_189 : Row := { vars := #[68, 271, 410, 277], coeff := #[1, 1, 1, 1], bound := 1, weight := 6098, edges := #[⟨0, 1, 385⟩, ⟨0, 2, 233⟩, ⟨0, 3, 378⟩, ⟨1, 2, 175⟩, ⟨1, 3, 304⟩, ⟨2, 3, 132⟩], triples := #[] }
def er069_190 : Row := { vars := #[71, 418, 163], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 224⟩, ⟨0, 2, 475⟩, ⟨1, 2, 119⟩], triples := #[] }
def er069_191 : Row := { vars := #[71, 186, 109], coeff := #[1, 1, 1], bound := 1, weight := 439025, edges := #[⟨0, 1, 467⟩, ⟨0, 2, 66⟩, ⟨1, 2, 433⟩], triples := #[] }
end HardyCapset20261020.Cert



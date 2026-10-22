-- Prove2me | Definitions.Def_HardyCapsetEvaluationData149rows02V420261021
-- name    : HardyCapsetEvaluationData149rows02V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:58:16.131155+00:00
-- url     : https://prove2.me/theorems/ebde7538-628c-4e38-9f86-a397ca2b33bd
-- title:
--   HardyCapsetEvaluationData149rows02V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er149_128 : Row := { vars := #[394, 398], coeff := #[1, 1], bound := 1, weight := 214286, edges := #[⟨0, 1, 441⟩], triples := #[] }
def er149_129 : Row := { vars := #[426, 428], coeff := #[1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 487⟩], triples := #[] }
def er149_130 : Row := { vars := #[431, 436], coeff := #[1, 1], bound := 1, weight := 357143, edges := #[⟨0, 1, 507⟩], triples := #[] }
def er149_131 : Row := { vars := #[0, 378, 250], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 333⟩, ⟨0, 2, 360⟩, ⟨1, 2, 185⟩], triples := #[] }
def er149_132 : Row := { vars := #[1, 268, 64], coeff := #[1, 1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 459⟩, ⟨0, 2, 27⟩, ⟨1, 2, 481⟩], triples := #[] }
def er149_133 : Row := { vars := #[1, 25, 104], coeff := #[1, 1, 1], bound := 1, weight := 678572, edges := #[⟨0, 1, 63⟩, ⟨0, 2, 158⟩, ⟨1, 2, 185⟩], triples := #[] }
def er149_134 : Row := { vars := #[3, 343, 347], coeff := #[1, 1, 1], bound := 1, weight := 678572, edges := #[⟨0, 1, 199⟩, ⟨0, 2, 215⟩, ⟨1, 2, 374⟩], triples := #[] }
def er149_135 : Row := { vars := #[4, 240, 249], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 363⟩, ⟨0, 2, 355⟩, ⟨1, 2, 193⟩], triples := #[] }
def er149_136 : Row := { vars := #[5, 345, 354], coeff := #[1, 1, 1], bound := 1, weight := 250000, edges := #[⟨0, 1, 203⟩, ⟨0, 2, 195⟩, ⟨1, 2, 354⟩], triples := #[] }
def er149_137 : Row := { vars := #[5, 108, 126], coeff := #[1, 1, 1], bound := 1, weight := 750001, edges := #[⟨0, 1, 157⟩, ⟨0, 2, 144⟩, ⟨1, 2, 76⟩], triples := #[] }
def er149_138 : Row := { vars := #[6, 132, 193, 188, 142], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 71429, edges := #[⟨0, 1, 188⟩, ⟨0, 2, 93⟩, ⟨0, 3, 96⟩, ⟨0, 4, 184⟩, ⟨1, 2, 67⟩, ⟨1, 3, 70⟩, ⟨1, 4, 117⟩, ⟨2, 3, 150⟩, ⟨2, 4, 57⟩, ⟨3, 4, 60⟩], triples := #[] }
def er149_139 : Row := { vars := #[6, 90, 18], coeff := #[1, 1, 1], bound := 1, weight := 107143, edges := #[⟨0, 1, 159⟩, ⟨0, 2, 69⟩, ⟨1, 2, 183⟩], triples := #[] }
def er149_140 : Row := { vars := #[6, 62, 438], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 18⟩, ⟨0, 2, 260⟩, ⟨1, 2, 284⟩], triples := #[] }
def er149_141 : Row := { vars := #[7, 131, 95, 78], coeff := #[1, 1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 189⟩, ⟨0, 2, 166⟩, ⟨0, 3, 20⟩, ⟨1, 2, 122⟩, ⟨1, 3, 164⟩, ⟨2, 3, 179⟩], triples := #[] }
def er149_142 : Row := { vars := #[8, 418, 216], coeff := #[1, 1, 1], bound := 1, weight := 750000, edges := #[⟨0, 1, 276⟩, ⟨0, 2, 128⟩, ⟨1, 2, 310⟩], triples := #[] }
def er149_143 : Row := { vars := #[9, 19, 187], coeff := #[1, 1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 57⟩, ⟨0, 2, 86⟩, ⟨1, 2, 130⟩], triples := #[] }
def er149_144 : Row := { vars := #[9, 151, 197], coeff := #[1, 1, 1], bound := 1, weight := 678572, edges := #[⟨0, 1, 189⟩, ⟨0, 2, 98⟩, ⟨1, 2, 65⟩], triples := #[] }
def er149_145 : Row := { vars := #[11, 147, 73, 112], coeff := #[1, 1, 1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 189⟩, ⟨0, 2, 13⟩, ⟨0, 3, 135⟩, ⟨1, 2, 144⟩, ⟨1, 3, 120⟩, ⟨2, 3, 173⟩], triples := #[] }
def er149_146 : Row := { vars := #[12, 155, 51], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 147⟩, ⟨0, 2, 20⟩, ⟨1, 2, 149⟩], triples := #[] }
def er149_147 : Row := { vars := #[13, 40, 371, 271], coeff := #[1, 1, 1, 1], bound := 1, weight := 500001, edges := #[⟨0, 1, 18⟩, ⟨0, 2, 333⟩, ⟨0, 3, 503⟩, ⟨1, 2, 334⟩, ⟨1, 3, 492⟩, ⟨2, 3, 98⟩], triples := #[] }
def er149_148 : Row := { vars := #[13, 40, 375, 267], coeff := #[1, 1, 1, 1], bound := 1, weight := 500001, edges := #[⟨0, 1, 18⟩, ⟨0, 2, 343⟩, ⟨0, 3, 493⟩, ⟨1, 2, 332⟩, ⟨1, 3, 494⟩, ⟨2, 3, 98⟩], triples := #[] }
def er149_149 : Row := { vars := #[14, 98, 233], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 180⟩, ⟨0, 2, 96⟩, ⟨1, 2, 17⟩], triples := #[] }
def er149_150 : Row := { vars := #[15, 214, 359], coeff := #[1, 1, 1], bound := 1, weight := 214286, edges := #[⟨0, 1, 116⟩, ⟨0, 2, 233⟩, ⟨1, 2, 262⟩], triples := #[] }
def er149_151 : Row := { vars := #[15, 221, 225], coeff := #[1, 1, 1], bound := 1, weight := 285715, edges := #[⟨0, 1, 82⟩, ⟨0, 2, 105⟩, ⟨1, 2, 189⟩], triples := #[] }
def er149_152 : Row := { vars := #[17, 38, 317], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 29⟩, ⟨0, 2, 435⟩, ⟨1, 2, 422⟩], triples := #[] }
def er149_153 : Row := { vars := #[24, 153, 420, 159, 316], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 159⟩, ⟨0, 2, 258⟩, ⟨0, 3, 149⟩, ⟨0, 4, 418⟩, ⟨1, 2, 215⟩, ⟨1, 3, 129⟩, ⟨1, 4, 375⟩, ⟨2, 3, 203⟩, ⟨2, 4, 174⟩, ⟨3, 4, 363⟩], triples := #[] }
def er149_154 : Row := { vars := #[25, 22, 91], coeff := #[1, 1, 1], bound := 1, weight := 71429, edges := #[⟨0, 1, 31⟩, ⟨0, 2, 189⟩, ⟨1, 2, 180⟩], triples := #[] }
def er149_155 : Row := { vars := #[32, 166, 152], coeff := #[1, 1, 1], bound := 1, weight := 214286, edges := #[⟨0, 1, 136⟩, ⟨0, 2, 171⟩, ⟨1, 2, 107⟩], triples := #[] }
def er149_156 : Row := { vars := #[32, 166, 18], coeff := #[1, 1, 1], bound := 1, weight := 785715, edges := #[⟨0, 1, 136⟩, ⟨0, 2, 32⟩, ⟨1, 2, 154⟩], triples := #[] }
def er149_157 : Row := { vars := #[33, 421, 156], coeff := #[1, 1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 266⟩, ⟨0, 2, 158⟩, ⟨1, 2, 218⟩], triples := #[] }
def er149_158 : Row := { vars := #[33, 372, 256], coeff := #[1, 1, 1], bound := 1, weight := 678572, edges := #[⟨0, 1, 351⟩, ⟨0, 2, 390⟩, ⟨1, 2, 191⟩], triples := #[] }
def er149_159 : Row := { vars := #[34, 282, 223], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 469⟩, ⟨0, 2, 107⟩, ⟨1, 2, 360⟩], triples := #[] }
def er149_160 : Row := { vars := #[35, 420, 316], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 260⟩, ⟨0, 2, 420⟩, ⟨1, 2, 174⟩], triples := #[] }
def er149_161 : Row := { vars := #[38, 268, 144], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 507⟩, ⟨0, 2, 174⟩, ⟨1, 2, 455⟩], triples := #[] }
def er149_162 : Row := { vars := #[39, 258, 419], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 363⟩, ⟨0, 2, 257⟩, ⟨1, 2, 101⟩], triples := #[] }
def er149_163 : Row := { vars := #[41, 163, 420, 165, 316], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 159⟩, ⟨0, 2, 257⟩, ⟨0, 3, 161⟩, ⟨0, 4, 417⟩, ⟨1, 2, 195⟩, ⟨1, 3, 129⟩, ⟨1, 4, 355⟩, ⟨2, 3, 199⟩, ⟨2, 4, 174⟩, ⟨3, 4, 359⟩], triples := #[] }
def er149_164 : Row := { vars := #[43, 324, 369, 167], coeff := #[1, 1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 435⟩, ⟨0, 2, 215⟩, ⟨0, 3, 164⟩, ⟨1, 2, 107⟩, ⟨1, 3, 374⟩, ⟨2, 3, 344⟩], triples := #[] }
def er149_165 : Row := { vars := #[49, 225, 124], coeff := #[1, 1, 1], bound := 1, weight := 357143, edges := #[⟨0, 1, 73⟩, ⟨0, 2, 191⟩, ⟨1, 2, 13⟩], triples := #[] }
def er149_166 : Row := { vars := #[53, 210, 143, 145, 66], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 821429, edges := #[⟨0, 1, 99⟩, ⟨0, 2, 167⟩, ⟨0, 3, 164⟩, ⟨0, 4, 62⟩, ⟨1, 2, 23⟩, ⟨1, 3, 20⟩, ⟨1, 4, 89⟩, ⟨2, 3, 114⟩, ⟨2, 4, 157⟩, ⟨3, 4, 154⟩], triples := #[] }
def er149_167 : Row := { vars := #[54, 441, 196], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 288⟩, ⟨0, 2, 115⟩, ⟨1, 2, 327⟩], triples := #[] }
def er149_168 : Row := { vars := #[55, 63, 68], coeff := #[1, 1, 1], bound := 1, weight := 285715, edges := #[⟨0, 1, 63⟩, ⟨0, 2, 65⟩, ⟨1, 2, 53⟩], triples := #[] }
def er149_169 : Row := { vars := #[55, 63, 362], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 63⟩, ⟨0, 2, 236⟩, ⟨1, 2, 241⟩], triples := #[] }
def er149_170 : Row := { vars := #[55, 63, 306], coeff := #[1, 1, 1], bound := 1, weight := 214286, edges := #[⟨0, 1, 63⟩, ⟨0, 2, 435⟩, ⟨1, 2, 425⟩], triples := #[] }
def er149_171 : Row := { vars := #[56, 214, 255], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 98⟩, ⟨0, 2, 382⟩, ⟨1, 2, 422⟩], triples := #[] }
def er149_172 : Row := { vars := #[57, 135, 278], coeff := #[1, 1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 135⟩, ⟨0, 2, 459⟩, ⟨1, 2, 417⟩], triples := #[] }
def er149_173 : Row := { vars := #[59, 213, 86], coeff := #[1, 1, 1], bound := 1, weight := 285715, edges := #[⟨0, 1, 98⟩, ⟨0, 2, 53⟩, ⟨1, 2, 78⟩], triples := #[] }
def er149_174 : Row := { vars := #[59, 109, 111], coeff := #[1, 1, 1], bound := 1, weight := 500001, edges := #[⟨0, 1, 179⟩, ⟨0, 2, 176⟩, ⟨1, 2, 93⟩], triples := #[] }
def er149_175 : Row := { vars := #[60, 67, 381], coeff := #[1, 1, 1], bound := 1, weight := 642858, edges := #[⟨0, 1, 68⟩, ⟨0, 2, 299⟩, ⟨1, 2, 307⟩], triples := #[] }
def er149_176 : Row := { vars := #[62, 289, 297], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 494⟩, ⟨0, 2, 492⟩, ⟨1, 2, 278⟩], triples := #[] }
def er149_177 : Row := { vars := #[64, 295, 435], coeff := #[1, 1, 1], bound := 1, weight := 678572, edges := #[⟨0, 1, 492⟩, ⟨0, 2, 285⟩, ⟨1, 2, 48⟩], triples := #[] }
def er149_178 : Row := { vars := #[67, 132, 142], coeff := #[1, 1, 1], bound := 1, weight := 35715, edges := #[⟨0, 1, 159⟩, ⟨0, 2, 149⟩, ⟨1, 2, 117⟩], triples := #[] }
def er149_179 : Row := { vars := #[67, 397, 381], coeff := #[1, 1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 341⟩, ⟨0, 2, 307⟩, ⟨1, 2, 412⟩], triples := #[] }
def er149_180 : Row := { vars := #[69, 388, 83], coeff := #[1, 1, 1], bound := 1, weight := 250001, edges := #[⟨0, 1, 299⟩, ⟨0, 2, 48⟩, ⟨1, 2, 306⟩], triples := #[] }
def er149_181 : Row := { vars := #[69, 272, 396], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 477⟩, ⟨0, 2, 341⟩, ⟨1, 2, 114⟩], triples := #[] }
def er149_182 : Row := { vars := #[70, 81, 84], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 48⟩, ⟨0, 2, 42⟩, ⟨1, 2, 70⟩], triples := #[] }
def er149_183 : Row := { vars := #[72, 84, 58], coeff := #[1, 1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 39⟩, ⟨0, 2, 68⟩, ⟨1, 2, 57⟩], triples := #[] }
def er149_184 : Row := { vars := #[73, 99, 359], coeff := #[1, 1, 1], bound := 1, weight := 392858, edges := #[⟨0, 1, 179⟩, ⟨0, 2, 210⟩, ⟨1, 2, 347⟩], triples := #[] }
def er149_185 : Row := { vars := #[74, 161, 376], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 184⟩, ⟨0, 2, 313⟩, ⟨1, 2, 266⟩], triples := #[] }
def er149_186 : Row := { vars := #[74, 386, 138], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 299⟩, ⟨0, 2, 166⟩, ⟨1, 2, 258⟩], triples := #[] }
def er149_187 : Row := { vars := #[80, 118, 256, 360, 121], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 177⟩, ⟨0, 2, 356⟩, ⟨0, 3, 196⟩, ⟨0, 4, 179⟩, ⟨1, 2, 492⟩, ⟨1, 3, 332⟩, ⟨1, 4, 98⟩, ⟨2, 3, 18⟩, ⟨2, 4, 493⟩, ⟨3, 4, 333⟩], triples := #[] }
def er149_188 : Row := { vars := #[81, 163, 364], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 189⟩, ⟨0, 2, 236⟩, ⟨1, 2, 331⟩], triples := #[] }
def er149_189 : Row := { vars := #[82, 79, 232], coeff := #[1, 1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 62⟩, ⟨0, 2, 130⟩, ⟨1, 2, 128⟩], triples := #[] }
def er149_190 : Row := { vars := #[87, 400, 262], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 344⟩, ⟨0, 2, 395⟩, ⟨1, 2, 183⟩], triples := #[] }
def er149_191 : Row := { vars := #[87, 61, 65], coeff := #[1, 1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 60⟩, ⟨0, 2, 39⟩, ⟨1, 2, 68⟩], triples := #[] }
end HardyCapset20261020.Cert



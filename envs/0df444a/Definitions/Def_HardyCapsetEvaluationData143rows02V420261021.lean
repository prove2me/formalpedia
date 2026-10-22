-- Prove2me | Definitions.Def_HardyCapsetEvaluationData143rows02V420261021
-- name    : HardyCapsetEvaluationData143rows02V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:49:06.453818+00:00
-- url     : https://prove2.me/theorems/8a420229-50e0-4686-9ee2-b05612a7aaea
-- title:
--   HardyCapsetEvaluationData143rows02V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er143_128 : Row := { vars := #[43, 286, 424], coeff := #[1, 1, 1], bound := 1, weight := 644445, edges := #[⟨0, 1, 459⟩, ⟨0, 2, 258⟩, ⟨1, 2, 55⟩], triples := #[] }
def er143_129 : Row := { vars := #[44, 228, 371], coeff := #[1, 1, 1], bound := 1, weight := 333334, edges := #[⟨0, 1, 130⟩, ⟨0, 2, 235⟩, ⟨1, 2, 289⟩], triples := #[] }
def er143_130 : Row := { vars := #[44, 267, 54], coeff := #[1, 1, 1], bound := 1, weight := 466667, edges := #[⟨0, 1, 395⟩, ⟨0, 2, 65⟩, ⟨1, 2, 401⟩], triples := #[] }
def er143_131 : Row := { vars := #[44, 378, 90], coeff := #[1, 1, 1], bound := 1, weight := 200000, edges := #[⟨0, 1, 309⟩, ⟨0, 2, 179⟩, ⟨1, 2, 251⟩], triples := #[] }
def er143_132 : Row := { vars := #[47, 61, 74], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 68⟩, ⟨0, 2, 57⟩, ⟨1, 2, 42⟩], triples := #[] }
def er143_133 : Row := { vars := #[50, 363, 304], coeff := #[1, 1, 1], bound := 1, weight := 666667, edges := #[⟨0, 1, 217⟩, ⟨0, 2, 504⟩, ⟨1, 2, 148⟩], triples := #[] }
def er143_134 : Row := { vars := #[50, 54, 119], coeff := #[1, 1, 1], bound := 1, weight := 333334, edges := #[⟨0, 1, 68⟩, ⟨0, 2, 133⟩, ⟨1, 2, 161⟩], triples := #[] }
def er143_135 : Row := { vars := #[51, 295, 424], coeff := #[1, 1, 1], bound := 1, weight := 644445, edges := #[⟨0, 1, 459⟩, ⟨0, 2, 256⟩, ⟨1, 2, 63⟩], triples := #[] }
def er143_136 : Row := { vars := #[53, 79, 259, 363, 92], coeff := #[1, 1, 1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 179⟩, ⟨0, 2, 360⟩, ⟨0, 3, 200⟩, ⟨0, 4, 175⟩, ⟨1, 2, 503⟩, ⟨1, 3, 343⟩, ⟨1, 4, 100⟩, ⟨2, 3, 16⟩, ⟨2, 4, 494⟩, ⟨3, 4, 334⟩], triples := #[] }
def er143_137 : Row := { vars := #[54, 415, 153], coeff := #[1, 1, 1], bound := 1, weight := 200001, edges := #[⟨0, 1, 333⟩, ⟨0, 2, 187⟩, ⟨1, 2, 279⟩], triples := #[] }
def er143_138 : Row := { vars := #[56, 120, 256], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 161⟩, ⟨0, 2, 374⟩, ⟨1, 2, 469⟩], triples := #[] }
def er143_139 : Row := { vars := #[64, 208, 418], coeff := #[1, 1, 1], bound := 1, weight := 88889, edges := #[⟨0, 1, 88⟩, ⟨0, 2, 269⟩, ⟨1, 2, 349⟩], triples := #[] }
def er143_140 : Row := { vars := #[67, 232, 70], coeff := #[1, 1, 1], bound := 1, weight := 600000, edges := #[⟨0, 1, 130⟩, ⟨0, 2, 64⟩, ⟨1, 2, 128⟩], triples := #[] }
def er143_141 : Row := { vars := #[67, 139, 275], coeff := #[1, 1, 1], bound := 1, weight := 400001, edges := #[⟨0, 1, 161⟩, ⟨0, 2, 469⟩, ⟨1, 2, 439⟩], triples := #[] }
def er143_142 : Row := { vars := #[68, 104, 259, 379], coeff := #[1, 1, 1, 1], bound := 1, weight := 377778, edges := #[⟨0, 1, 179⟩, ⟨0, 2, 352⟩, ⟨0, 3, 311⟩, ⟨1, 2, 493⟩, ⟨1, 3, 245⟩, ⟨2, 3, 187⟩], triples := #[] }
def er143_143 : Row := { vars := #[68, 310, 368], coeff := #[1, 1, 1], bound := 1, weight := 622223, edges := #[⟨0, 1, 503⟩, ⟨0, 2, 221⟩, ⟨1, 2, 165⟩], triples := #[] }
def er143_144 : Row := { vars := #[78, 88, 89], coeff := #[1, 1, 1], bound := 1, weight := 866667, edges := #[⟨0, 1, 101⟩, ⟨0, 2, 99⟩, ⟨1, 2, 91⟩], triples := #[] }
def er143_145 : Row := { vars := #[78, 88, 202], coeff := #[1, 1, 1], bound := 1, weight := 133334, edges := #[⟨0, 1, 101⟩, ⟨0, 2, 43⟩, ⟨1, 2, 68⟩], triples := #[] }
def er143_146 : Row := { vars := #[82, 199, 93], coeff := #[1, 1, 1], bound := 1, weight := 88889, edges := #[⟨0, 1, 45⟩, ⟨0, 2, 107⟩, ⟨1, 2, 65⟩], triples := #[] }
def er143_147 : Row := { vars := #[82, 392, 220], coeff := #[1, 1, 1], bound := 1, weight := 911112, edges := #[⟨0, 1, 276⟩, ⟨0, 2, 6⟩, ⟨1, 2, 192⟩], triples := #[] }
def er143_148 : Row := { vars := #[85, 102, 215], coeff := #[1, 1, 1], bound := 1, weight := 755556, edges := #[⟨0, 1, 105⟩, ⟨0, 2, 60⟩, ⟨1, 2, 50⟩], triples := #[] }
def er143_149 : Row := { vars := #[86, 221, 287], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 14⟩, ⟨0, 2, 436⟩, ⟨1, 2, 352⟩], triples := #[] }
def er143_150 : Row := { vars := #[90, 274, 319], coeff := #[1, 1, 1], bound := 1, weight := 800001, edges := #[⟨0, 1, 411⟩, ⟨0, 2, 359⟩, ⟨1, 2, 203⟩], triples := #[] }
def er143_151 : Row := { vars := #[93, 199, 267, 409], coeff := #[1, 1, 1, 1], bound := 1, weight := 533334, edges := #[⟨0, 1, 65⟩, ⟨0, 2, 481⟩, ⟨0, 3, 258⟩, ⟨1, 2, 405⟩, ⟨1, 3, 215⟩, ⟨2, 3, 189⟩], triples := #[] }
def er143_152 : Row := { vars := #[93, 199, 349], coeff := #[1, 1, 1], bound := 1, weight := 200000, edges := #[⟨0, 1, 65⟩, ⟨0, 2, 304⟩, ⟨1, 2, 297⟩], triples := #[] }
def er143_153 : Row := { vars := #[94, 110, 214], coeff := #[1, 1, 1], bound := 1, weight := 666667, edges := #[⟨0, 1, 77⟩, ⟨0, 2, 39⟩, ⟨1, 2, 67⟩], triples := #[] }
def er143_154 : Row := { vars := #[94, 212, 229], coeff := #[1, 1, 1], bound := 1, weight := 333334, edges := #[⟨0, 1, 49⟩, ⟨0, 2, 9⟩, ⟨1, 2, 161⟩], triples := #[] }
def er143_155 : Row := { vars := #[95, 203, 111], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 60⟩, ⟨0, 2, 79⟩, ⟨1, 2, 50⟩], triples := #[] }
def er143_156 : Row := { vars := #[96, 135, 344], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 125⟩, ⟨0, 2, 304⟩, ⟨1, 2, 338⟩], triples := #[] }
def er143_157 : Row := { vars := #[99, 258, 429], coeff := #[1, 1, 1], bound := 1, weight := 88889, edges := #[⟨0, 1, 498⟩, ⟨0, 2, 239⟩, ⟨1, 2, 113⟩], triples := #[] }
def er143_158 : Row := { vars := #[99, 105, 229], coeff := #[1, 1, 1], bound := 1, weight := 666667, edges := #[⟨0, 1, 77⟩, ⟨0, 2, 1⟩, ⟨1, 2, 29⟩], triples := #[] }
def er143_159 : Row := { vars := #[100, 106, 400], coeff := #[1, 1, 1], bound := 1, weight := 88889, edges := #[⟨0, 1, 77⟩, ⟨0, 2, 276⟩, ⟨1, 2, 295⟩], triples := #[] }
def er143_160 : Row := { vars := #[101, 408, 237], coeff := #[1, 1, 1], bound := 1, weight := 844445, edges := #[⟨0, 1, 259⟩, ⟨0, 2, 466⟩, ⟨1, 2, 177⟩], triples := #[] }
def er143_161 : Row := { vars := #[101, 114, 121], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 83⟩, ⟨0, 2, 131⟩, ⟨1, 2, 126⟩], triples := #[] }
def er143_162 : Row := { vars := #[102, 140, 215], coeff := #[1, 1, 1], bound := 1, weight := 244445, edges := #[⟨0, 1, 120⟩, ⟨0, 2, 50⟩, ⟨1, 2, 31⟩], triples := #[] }
def er143_163 : Row := { vars := #[104, 231, 107], coeff := #[1, 1, 1], bound := 1, weight := 288889, edges := #[⟨0, 1, 29⟩, ⟨0, 2, 100⟩, ⟨1, 2, 27⟩], triples := #[] }
def er143_164 : Row := { vars := #[104, 105, 275], coeff := #[1, 1, 1], bound := 1, weight := 333334, edges := #[⟨0, 1, 101⟩, ⟨0, 2, 405⟩, ⟨1, 2, 407⟩], triples := #[] }
def er143_165 : Row := { vars := #[107, 272, 260], coeff := #[1, 1, 1], bound := 1, weight := 333334, edges := #[⟨0, 1, 481⟩, ⟨0, 2, 490⟩, ⟨1, 2, 199⟩], triples := #[] }
def er143_166 : Row := { vars := #[108, 210, 305, 420], coeff := #[1, 1, 1, 1], bound := 1, weight := 911112, edges := #[⟨0, 1, 65⟩, ⟨0, 2, 416⟩, ⟨0, 3, 197⟩, ⟨1, 2, 359⟩, ⟨1, 3, 330⟩, ⟨2, 3, 19⟩], triples := #[] }
def er143_167 : Row := { vars := #[108, 210, 305, 372], coeff := #[1, 1, 1, 1], bound := 1, weight := 88889, edges := #[⟨0, 1, 65⟩, ⟨0, 2, 416⟩, ⟨0, 3, 311⟩, ⟨1, 2, 359⟩, ⟨1, 3, 245⟩, ⟨2, 3, 187⟩], triples := #[] }
def er143_168 : Row := { vars := #[115, 201, 218], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 55⟩, ⟨0, 2, 20⟩, ⟨1, 2, 144⟩], triples := #[] }
def er143_169 : Row := { vars := #[116, 289, 414], coeff := #[1, 1, 1], bound := 1, weight := 955556, edges := #[⟨0, 1, 436⟩, ⟨0, 2, 270⟩, ⟨1, 2, 81⟩], triples := #[] }
def er143_170 : Row := { vars := #[117, 46, 60], coeff := #[1, 1, 1], bound := 1, weight := 777778, edges := #[⟨0, 1, 144⟩, ⟨0, 2, 167⟩, ⟨1, 2, 66⟩], triples := #[] }
def er143_171 : Row := { vars := #[117, 342, 347], coeff := #[1, 1, 1], bound := 1, weight := 222223, edges := #[⟨0, 1, 332⟩, ⟨0, 2, 343⟩, ⟨1, 2, 374⟩], triples := #[] }
def er143_172 : Row := { vars := #[118, 166, 180], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 47⟩, ⟨0, 2, 70⟩, ⟨1, 2, 163⟩], triples := #[] }
def er143_173 : Row := { vars := #[118, 169, 185], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 39⟩, ⟨0, 2, 67⟩, ⟨1, 2, 166⟩], triples := #[] }
def er143_174 : Row := { vars := #[118, 341, 346], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 332⟩, ⟨0, 2, 343⟩, ⟨1, 2, 373⟩], triples := #[] }
def er143_175 : Row := { vars := #[119, 175, 130], coeff := #[1, 1, 1], bound := 1, weight := 666667, edges := #[⟨0, 1, 65⟩, ⟨0, 2, 118⟩, ⟨1, 2, 55⟩], triples := #[] }
def er143_176 : Row := { vars := #[122, 155, 184], coeff := #[1, 1, 1], bound := 1, weight := 711112, edges := #[⟨0, 1, 100⟩, ⟨0, 2, 63⟩, ⟨1, 2, 23⟩], triples := #[] }
def er143_177 : Row := { vars := #[122, 155, 194], coeff := #[1, 1, 1], bound := 1, weight := 200001, edges := #[⟨0, 1, 100⟩, ⟨0, 2, 55⟩, ⟨1, 2, 10⟩], triples := #[] }
def er143_178 : Row := { vars := #[123, 392, 46], coeff := #[1, 1, 1], bound := 1, weight := 88889, edges := #[⟨0, 1, 256⟩, ⟨0, 2, 138⟩, ⟨1, 2, 299⟩], triples := #[] }
def er143_179 : Row := { vars := #[123, 177, 298], coeff := #[1, 1, 1], bound := 1, weight := 911112, edges := #[⟨0, 1, 66⟩, ⟨0, 2, 418⟩, ⟨1, 2, 395⟩], triples := #[] }
def er143_180 : Row := { vars := #[124, 170, 197], coeff := #[1, 1, 1], bound := 1, weight := 600001, edges := #[⟨0, 1, 68⟩, ⟨0, 2, 7⟩, ⟨1, 2, 190⟩], triples := #[] }
def er143_181 : Row := { vars := #[124, 439, 441], coeff := #[1, 1, 1], bound := 1, weight := 400000, edges := #[⟨0, 1, 197⟩, ⟨0, 2, 213⟩, ⟨1, 2, 507⟩], triples := #[] }
def er143_182 : Row := { vars := #[126, 296, 182], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 418⟩, ⟨0, 2, 69⟩, ⟨1, 2, 395⟩], triples := #[] }
def er143_183 : Row := { vars := #[127, 241, 250], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 494⟩, ⟨0, 2, 493⟩, ⟨1, 2, 198⟩], triples := #[] }
def er143_184 : Row := { vars := #[129, 391, 302], coeff := #[1, 1, 1], bound := 1, weight := 866667, edges := #[⟨0, 1, 275⟩, ⟨0, 2, 411⟩, ⟨1, 2, 81⟩], triples := #[] }
def er143_185 : Row := { vars := #[131, 288, 427], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 430⟩, ⟨0, 2, 231⟩, ⟨1, 2, 1⟩], triples := #[] }
def er143_186 : Row := { vars := #[132, 193, 191], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 49⟩, ⟨0, 2, 45⟩, ⟨1, 2, 164⟩], triples := #[] }
def er143_187 : Row := { vars := #[133, 350, 276], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 334⟩, ⟨0, 2, 447⟩, ⟨1, 2, 154⟩], triples := #[] }
def er143_188 : Row := { vars := #[134, 136, 277, 345], coeff := #[1, 1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 113⟩, ⟨0, 2, 447⟩, ⟨0, 3, 342⟩, ⟨1, 2, 443⟩, ⟨1, 3, 338⟩, ⟨2, 3, 151⟩], triples := #[] }
def er143_189 : Row := { vars := #[141, 361, 186], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 311⟩, ⟨0, 2, 65⟩, ⟨1, 2, 276⟩], triples := #[] }
def er143_190 : Row := { vars := #[142, 196, 375, 271], coeff := #[1, 1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 66⟩, ⟨0, 2, 305⟩, ⟨0, 3, 465⟩, ⟨1, 2, 270⟩, ⟨1, 3, 430⟩, ⟨2, 3, 65⟩], triples := #[] }
def er143_191 : Row := { vars := #[143, 149, 314], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 130⟩, ⟨0, 2, 387⟩, ⟨1, 2, 391⟩], triples := #[] }
end HardyCapset20261020.Cert



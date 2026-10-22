-- Prove2me | Definitions.Def_HardyCapsetEvaluationData016rows02V420261021
-- name    : HardyCapsetEvaluationData016rows02V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T01:47:35.004859+00:00
-- url     : https://prove2.me/theorems/b60eb886-54d3-49c8-a282-5300a9854234
-- title:
--   HardyCapsetEvaluationData016rows02V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er016_128 : Row := { vars := #[19, 68, 315], coeff := #[1, 1, 1], bound := 1, weight := 429457, edges := #[⟨0, 1, 464⟩, ⟨0, 2, 275⟩, ⟨1, 2, 170⟩], triples := #[] }
def er016_129 : Row := { vars := #[24, 50, 275], coeff := #[1, 1, 1], bound := 1, weight := 414798, edges := #[⟨0, 1, 412⟩, ⟨0, 2, 217⟩, ⟨1, 2, 152⟩], triples := #[] }
def er016_130 : Row := { vars := #[25, 97, 378], coeff := #[1, 1, 1], bound := 1, weight := 271055, edges := #[⟨0, 1, 358⟩, ⟨0, 2, 313⟩, ⟨1, 2, 17⟩], triples := #[] }
def er016_131 : Row := { vars := #[25, 52, 273], coeff := #[1, 1, 1], bound := 1, weight := 271055, edges := #[⟨0, 1, 412⟩, ⟨0, 2, 198⟩, ⟨1, 2, 158⟩], triples := #[] }
def er016_132 : Row := { vars := #[27, 67, 278], coeff := #[1, 1, 1], bound := 1, weight := 1000001, edges := #[⟨0, 1, 410⟩, ⟨0, 2, 209⟩, ⟨1, 2, 165⟩], triples := #[] }
def er016_133 : Row := { vars := #[28, 96, 371], coeff := #[1, 1, 1], bound := 1, weight := 479831, edges := #[⟨0, 1, 354⟩, ⟨0, 2, 327⟩, ⟨1, 2, 29⟩], triples := #[] }
def er016_134 : Row := { vars := #[29, 102, 244], coeff := #[1, 1, 1], bound := 1, weight := 209367, edges := #[⟨0, 1, 370⟩, ⟨0, 2, 250⟩, ⟨1, 2, 167⟩], triples := #[] }
def er016_135 : Row := { vars := #[34, 269, 326], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 17⟩, ⟨0, 2, 174⟩, ⟨1, 2, 509⟩], triples := #[] }
def er016_136 : Row := { vars := #[34, 119, 314], coeff := #[1, 1, 1], bound := 1, weight := 813165, edges := #[⟨0, 1, 342⟩, ⟨0, 2, 178⟩, ⟨1, 2, 72⟩], triples := #[] }
def er016_137 : Row := { vars := #[35, 352, 289], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 128⟩, ⟨0, 2, 191⟩, ⟨1, 2, 390⟩], triples := #[] }
def er016_138 : Row := { vars := #[35, 177, 373], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 288⟩, ⟨0, 2, 118⟩, ⟨1, 2, 132⟩], triples := #[] }
def er016_139 : Row := { vars := #[36, 385, 384], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 113⟩, ⟨0, 2, 115⟩, ⟨1, 2, 511⟩], triples := #[] }
def er016_140 : Row := { vars := #[36, 376, 313], coeff := #[1, 1, 1], bound := 1, weight := 977470, edges := #[⟨0, 1, 117⟩, ⟨0, 2, 178⟩, ⟨1, 2, 400⟩], triples := #[] }
def er016_141 : Row := { vars := #[37, 259, 360], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 52⟩, ⟨0, 2, 126⟩, ⟨1, 2, 435⟩], triples := #[] }
def er016_142 : Row := { vars := #[43, 167, 380], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 290⟩, ⟨0, 2, 110⟩, ⟨1, 2, 148⟩], triples := #[] }
def er016_143 : Row := { vars := #[44, 131, 384], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 328⟩, ⟨0, 2, 109⟩, ⟨1, 2, 54⟩], triples := #[] }
def er016_144 : Row := { vars := #[46, 130, 329], coeff := #[1, 1, 1], bound := 1, weight := 338450, edges := #[⟨0, 1, 328⟩, ⟨0, 2, 100⟩, ⟨1, 2, 8⟩], triples := #[] }
def er016_145 : Row := { vars := #[46, 157, 304], coeff := #[1, 1, 1], bound := 1, weight := 357930, edges := #[⟨0, 1, 250⟩, ⟨0, 2, 178⟩, ⟨1, 2, 33⟩], triples := #[] }
def er016_146 : Row := { vars := #[46, 157, 281], coeff := #[1, 1, 1], bound := 1, weight := 172964, edges := #[⟨0, 1, 250⟩, ⟨0, 2, 191⟩, ⟨1, 2, 71⟩], triples := #[] }
def er016_147 : Row := { vars := #[46, 51, 251], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 211⟩, ⟨0, 2, 64⟩, ⟨1, 2, 69⟩], triples := #[] }
def er016_148 : Row := { vars := #[47, 138, 363], coeff := #[1, 1, 1], bound := 1, weight := 799587, edges := #[⟨0, 1, 314⟩, ⟨0, 2, 117⟩, ⟨1, 2, 67⟩], triples := #[] }
def er016_149 : Row := { vars := #[47, 139, 362], coeff := #[1, 1, 1], bound := 1, weight := 440280, edges := #[⟨0, 1, 313⟩, ⟨0, 2, 116⟩, ⟨1, 2, 68⟩], triples := #[] }
def er016_150 : Row := { vars := #[47, 190, 271], coeff := #[1, 1, 1], bound := 1, weight := 204054, edges := #[⟨0, 1, 268⟩, ⟨0, 2, 158⟩, ⟨1, 2, 1⟩], triples := #[] }
def er016_151 : Row := { vars := #[53, 135, 367], coeff := #[1, 1, 1], bound := 1, weight := 728946, edges := #[⟨0, 1, 313⟩, ⟨0, 2, 118⟩, ⟨1, 2, 63⟩], triples := #[] }
def er016_152 : Row := { vars := #[56, 135, 285], coeff := #[1, 1, 1], bound := 1, weight := 271055, edges := #[⟨0, 1, 315⟩, ⟨0, 2, 191⟩, ⟨1, 2, 98⟩], triples := #[] }
def er016_153 : Row := { vars := #[58, 107, 314], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 342⟩, ⟨0, 2, 168⟩, ⟨1, 2, 100⟩], triples := #[] }
def er016_154 : Row := { vars := #[58, 107, 348], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 342⟩, ⟨0, 2, 121⟩, ⟨1, 2, 28⟩], triples := #[] }
def er016_155 : Row := { vars := #[60, 131, 289], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 320⟩, ⟨0, 2, 180⟩, ⟨1, 2, 101⟩], triples := #[] }
def er016_156 : Row := { vars := #[60, 287, 133], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 182⟩, ⟨0, 2, 314⟩, ⟨1, 2, 99⟩], triples := #[] }
def er016_157 : Row := { vars := #[62, 261, 180], coeff := #[1, 1, 1], bound := 1, weight := 880559, edges := #[⟨0, 1, 18⟩, ⟨0, 2, 295⟩, ⟨1, 2, 95⟩], triples := #[] }
def er016_158 : Row := { vars := #[62, 145, 280], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 328⟩, ⟨0, 2, 186⟩, ⟨1, 2, 96⟩], triples := #[] }
def er016_159 : Row := { vars := #[71, 208, 307], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 274⟩, ⟨0, 2, 172⟩, ⟨1, 2, 54⟩], triples := #[] }
def er016_160 : Row := { vars := #[74, 315, 223], coeff := #[1, 1, 1], bound := 1, weight := 186836, edges := #[⟨0, 1, 164⟩, ⟨0, 2, 63⟩, ⟨1, 2, 473⟩], triples := #[] }
def er016_161 : Row := { vars := #[75, 222, 227], coeff := #[1, 1, 1], bound := 1, weight := 186836, edges := #[⟨0, 1, 64⟩, ⟨0, 2, 69⟩, ⟨1, 2, 371⟩], triples := #[] }
def er016_162 : Row := { vars := #[80, 111, 216], coeff := #[1, 1, 1], bound := 1, weight := 792602, edges := #[⟨0, 1, 315⟩, ⟨0, 2, 65⟩, ⟨1, 2, 188⟩], triples := #[] }
def er016_163 : Row := { vars := #[83, 212, 126], coeff := #[1, 1, 1], bound := 1, weight := 559721, edges := #[⟨0, 1, 53⟩, ⟨0, 2, 329⟩, ⟨1, 2, 186⟩], triples := #[] }
def er016_164 : Row := { vars := #[90, 193, 215], coeff := #[1, 1, 1], bound := 1, weight := 690378, edges := #[⟨0, 1, 281⟩, ⟨0, 2, 28⟩, ⟨1, 2, 116⟩], triples := #[] }
def er016_165 : Row := { vars := #[93, 210, 150], coeff := #[1, 1, 1], bound := 1, weight := 653779, edges := #[⟨0, 1, 17⟩, ⟨0, 2, 349⟩, ⟨1, 2, 174⟩], triples := #[] }
def er016_166 : Row := { vars := #[95, 222, 227], coeff := #[1, 1, 1], bound := 1, weight := 626329, edges := #[⟨0, 1, 160⟩, ⟨0, 2, 165⟩, ⟨1, 2, 371⟩], triples := #[] }
def er016_167 : Row := { vars := #[110, 355, 38], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 8⟩, ⟨0, 2, 344⟩, ⟨1, 2, 125⟩], triples := #[] }
def er016_168 : Row := { vars := #[113, 142, 212], coeff := #[1, 1, 1], bound := 1, weight := 440280, edges := #[⟨0, 1, 250⟩, ⟨0, 2, 190⟩, ⟨1, 2, 177⟩], triples := #[] }
def er016_169 : Row := { vars := #[116, 173, 211], coeff := #[1, 1, 1], bound := 1, weight := 897777, edges := #[⟨0, 1, 230⟩, ⟨0, 2, 189⟩, ⟨1, 2, 130⟩], triples := #[] }
def er016_170 : Row := { vars := #[117, 138, 210], coeff := #[1, 1, 1], bound := 1, weight := 200414, edges := #[⟨0, 1, 250⟩, ⟨0, 2, 189⟩, ⟨1, 2, 178⟩], triples := #[] }
def er016_171 : Row := { vars := #[119, 38, 345], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 337⟩, ⟨0, 2, 8⟩, ⟨1, 2, 129⟩], triples := #[] }
def er016_172 : Row := { vars := #[123, 202, 343], coeff := #[1, 1, 1], bound := 1, weight := 241539, edges := #[⟨0, 1, 218⟩, ⟨0, 2, 19⟩, ⟨1, 2, 149⟩], triples := #[] }
def er016_173 : Row := { vars := #[126, 127, 341], coeff := #[1, 1, 1], bound := 1, weight := 440280, edges := #[⟨0, 1, 273⟩, ⟨0, 2, 19⟩, ⟨1, 2, 17⟩], triples := #[] }
def er016_174 : Row := { vars := #[128, 336, 239], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 20⟩, ⟨0, 2, 172⟩, ⟨1, 2, 412⟩], triples := #[] }
def er016_175 : Row := { vars := #[129, 222, 306], coeff := #[1, 1, 1], bound := 1, weight := 186836, edges := #[⟨0, 1, 179⟩, ⟨0, 2, 122⟩, ⟨1, 2, 488⟩], triples := #[] }
def er016_176 : Row := { vars := #[136, 52, 285], coeff := #[1, 1, 1], bound := 1, weight := 728946, edges := #[⟨0, 1, 315⟩, ⟨0, 2, 100⟩, ⟨1, 2, 189⟩], triples := #[] }
def er016_177 : Row := { vars := #[136, 89, 214], coeff := #[1, 1, 1], bound := 1, weight := 271055, edges := #[⟨0, 1, 335⟩, ⟨0, 2, 178⟩, ⟨1, 2, 27⟩], triples := #[] }
def er016_178 : Row := { vars := #[142, 172, 365], coeff := #[1, 1, 1], bound := 1, weight := 559721, edges := #[⟨0, 1, 209⟩, ⟨0, 2, 62⟩, ⟨1, 2, 161⟩], triples := #[] }
def er016_179 : Row := { vars := #[165, 303, 242], coeff := #[1, 1, 1], bound := 1, weight := 813165, edges := #[⟨0, 1, 17⟩, ⟨0, 2, 126⟩, ⟨1, 2, 510⟩], triples := #[] }
def er016_180 : Row := { vars := #[171, 200, 211], coeff := #[1, 1, 1], bound := 1, weight := 102224, edges := #[⟨0, 1, 304⟩, ⟨0, 2, 131⟩, ⟨1, 2, 116⟩], triples := #[] }
def er016_181 : Row := { vars := #[172, 237, 365], coeff := #[1, 1, 1], bound := 1, weight := 440280, edges := #[⟨0, 1, 120⟩, ⟨0, 2, 161⟩, ⟨1, 2, 426⟩], triples := #[] }
def er016_182 : Row := { vars := #[181, 204, 215], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 306⟩, ⟨0, 2, 127⟩, ⟨1, 2, 112⟩], triples := #[] }
def er016_183 : Row := { vars := #[182, 146, 367], coeff := #[1, 1, 1], bound := 1, weight := 138529, edges := #[⟨0, 1, 217⟩, ⟨0, 2, 151⟩, ⟨1, 2, 52⟩], triples := #[] }
def er016_184 : Row := { vars := #[182, 179, 214], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 322⟩, ⟨0, 2, 127⟩, ⟨1, 2, 125⟩], triples := #[] }
def er016_185 : Row := { vars := #[184, 218, 283], coeff := #[1, 1, 1], bound := 1, weight := 500984, edges := #[⟨0, 1, 121⟩, ⟨0, 2, 18⟩, ⟨1, 2, 511⟩], triples := #[] }
def er016_186 : Row := { vars := #[194, 50, 309], coeff := #[1, 1, 1], bound := 1, weight := 440280, edges := #[⟨0, 1, 260⟩, ⟨0, 2, 64⟩, ⟨1, 2, 176⟩], triples := #[] }
def er016_187 : Row := { vars := #[206, 179, 217], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 306⟩, ⟨0, 2, 115⟩, ⟨1, 2, 124⟩], triples := #[] }
def er016_188 : Row := { vars := #[207, 121, 343], coeff := #[1, 1, 1], bound := 1, weight := 227962, edges := #[⟨0, 1, 217⟩, ⟨0, 2, 150⟩, ⟨1, 2, 16⟩], triples := #[] }
def er016_189 : Row := { vars := #[219, 343, 204], coeff := #[1, 1, 1], bound := 1, weight := 530500, edges := #[⟨0, 1, 450⟩, ⟨0, 2, 110⟩, ⟨1, 2, 148⟩], triples := #[] }
def er016_190 : Row := { vars := #[220, 309, 120], coeff := #[1, 1, 1], bound := 1, weight := 559721, edges := #[⟨0, 1, 482⟩, ⟨0, 2, 182⟩, ⟨1, 2, 89⟩], triples := #[] }
def er016_191 : Row := { vars := #[288, 255, 40], coeff := #[1, 1, 1], bound := 1, weight := 853011, edges := #[⟨0, 1, 475⟩, ⟨0, 2, 190⟩, ⟨1, 2, 63⟩], triples := #[] }
end HardyCapset20261020.Cert



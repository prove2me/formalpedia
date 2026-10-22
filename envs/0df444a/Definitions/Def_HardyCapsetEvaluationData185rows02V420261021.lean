-- Prove2me | Definitions.Def_HardyCapsetEvaluationData185rows02V420261021
-- name    : HardyCapsetEvaluationData185rows02V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:48:52.081989+00:00
-- url     : https://prove2.me/theorems/ee3a2a93-f3a1-4427-add1-fbf80343e5e6
-- title:
--   HardyCapsetEvaluationData185rows02V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er185_128 : Row := { vars := #[75, 116, 140, 123, 124], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 982143, edges := #[⟨3, 4, 268⟩, ⟨0, 3, 347⟩, ⟨1, 3, 293⟩, ⟨0, 4, 337⟩, ⟨1, 4, 283⟩], triples := #[⟨0, 1, 2⟩] }
def er185_129 : Row := { vars := #[87, 112, 151, 184], coeff := #[1, 1, 1, 1], bound := 2, weight := 660715, edges := #[⟨0, 3, 58⟩, ⟨1, 3, 148⟩], triples := #[⟨0, 1, 2⟩] }
def er185_130 : Row := { vars := #[91, 127, 141, 170, 174], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 339286, edges := #[⟨3, 4, 356⟩, ⟨1, 3, 178⟩, ⟨2, 3, 77⟩, ⟨0, 4, 44⟩, ⟨2, 4, 103⟩], triples := #[⟨0, 1, 2⟩] }
def er185_131 : Row := { vars := #[103, 122, 142, 181], coeff := #[1, 1, 1, 1], bound := 2, weight := 535715, edges := #[⟨0, 3, 6⟩, ⟨2, 3, 101⟩], triples := #[⟨0, 1, 2⟩] }
def er185_132 : Row := { vars := #[107, 122, 139, 170, 173], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 303572, edges := #[⟨3, 4, 357⟩, ⟨0, 3, 7⟩, ⟨1, 3, 191⟩, ⟨0, 4, 31⟩, ⟨2, 4, 80⟩], triples := #[⟨0, 1, 2⟩] }
def er185_133 : Row := { vars := #[158, 165, 167, 134], coeff := #[1, 1, 1, 1], bound := 2, weight := 285715, edges := #[⟨1, 3, 87⟩, ⟨2, 3, 78⟩], triples := #[⟨0, 1, 2⟩] }
def er185_134 : Row := { vars := #[166, 216, 291, 98, 185], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 107143, edges := #[⟨3, 4, 22⟩, ⟨0, 3, 7⟩, ⟨1, 3, 163⟩, ⟨0, 4, 368⟩, ⟨2, 4, 432⟩], triples := #[⟨0, 1, 2⟩] }
def er185_135 : Row := { vars := #[167, 247, 262, 97, 186], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 464286, edges := #[⟨3, 4, 22⟩, ⟨0, 3, 7⟩, ⟨2, 3, 103⟩, ⟨0, 4, 369⟩, ⟨1, 4, 486⟩], triples := #[⟨0, 1, 2⟩] }
def er185_136 : Row := { vars := #[168, 216, 290, 187, 28], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 571429, edges := #[⟨3, 4, 302⟩, ⟨0, 3, 370⟩, ⟨2, 3, 432⟩, ⟨0, 4, 301⟩, ⟨1, 4, 289⟩], triples := #[⟨0, 1, 2⟩] }
def er185_137 : Row := { vars := #[168, 235, 272, 85], coeff := #[1, 1, 1, 1], bound := 2, weight := 428572, edges := #[⟨0, 3, 42⟩, ⟨1, 3, 162⟩], triples := #[⟨0, 1, 2⟩] }
def er185_138 : Row := { vars := #[169, 236, 273, 27, 188], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 785715, edges := #[⟨3, 4, 302⟩, ⟨0, 3, 301⟩, ⟨1, 3, 267⟩, ⟨0, 4, 371⟩, ⟨2, 4, 454⟩], triples := #[⟨0, 1, 2⟩] }
def er185_139 : Row := { vars := #[169, 236, 273, 133, 188], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 53572, edges := #[⟨3, 4, 92⟩, ⟨0, 3, 77⟩, ⟨1, 3, 30⟩, ⟨0, 4, 371⟩, ⟨2, 4, 454⟩], triples := #[⟨0, 1, 2⟩] }
def er185_140 : Row := { vars := #[170, 205, 253, 286, 95], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 103⟩, ⟨0, 3, 417⟩, ⟨1, 3, 389⟩, ⟨0, 4, 43⟩, ⟨2, 4, 131⟩], triples := #[⟨0, 1, 2⟩] }
def er185_141 : Row := { vars := #[170, 208, 250, 107, 222], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 125001, edges := #[⟨3, 4, 164⟩, ⟨0, 3, 7⟩, ⟨1, 3, 179⟩, ⟨0, 4, 493⟩, ⟨2, 4, 399⟩], triples := #[⟨0, 1, 2⟩] }
def er185_142 : Row := { vars := #[173, 242, 270, 151], coeff := #[1, 1, 1, 1], bound := 2, weight := 339286, edges := #[⟨1, 3, 60⟩, ⟨2, 3, 154⟩], triples := #[⟨0, 1, 2⟩] }
def er185_143 : Row := { vars := #[175, 181, 186, 90, 157], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 464286, edges := #[⟨3, 4, 39⟩, ⟨0, 3, 58⟩, ⟨1, 3, 53⟩, ⟨0, 4, 363⟩, ⟨2, 4, 367⟩], triples := #[⟨0, 1, 2⟩] }
def er185_144 : Row := { vars := #[175, 182, 185, 160, 102], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 892858, edges := #[⟨3, 4, 2⟩, ⟨0, 3, 360⟩, ⟨2, 3, 366⟩, ⟨0, 4, 22⟩, ⟨1, 4, 16⟩], triples := #[⟨0, 1, 2⟩] }
def er185_145 : Row := { vars := #[175, 194, 202, 114, 255], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 375001, edges := #[⟨3, 4, 40⟩, ⟨0, 3, 153⟩, ⟨1, 3, 185⟩, ⟨0, 4, 440⟩, ⟨2, 4, 409⟩], triples := #[⟨0, 1, 2⟩] }
def er185_146 : Row := { vars := #[175, 208, 254, 229, 90], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 535715, edges := #[⟨3, 4, 135⟩, ⟨0, 3, 472⟩, ⟨2, 3, 389⟩, ⟨0, 4, 58⟩, ⟨1, 4, 185⟩], triples := #[⟨0, 1, 2⟩] }
def er185_147 : Row := { vars := #[175, 224, 289, 228, 137], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 464286, edges := #[⟨3, 4, 60⟩, ⟨0, 3, 505⟩, ⟨2, 3, 383⟩, ⟨0, 4, 94⟩, ⟨1, 4, 53⟩], triples := #[⟨0, 1, 2⟩] }
def er185_148 : Row := { vars := #[175, 244, 269, 227, 138], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 892858, edges := #[⟨3, 4, 59⟩, ⟨0, 3, 506⟩, ⟨1, 3, 413⟩, ⟨0, 4, 93⟩, ⟨2, 4, 184⟩], triples := #[⟨0, 1, 2⟩] }
def er185_149 : Row := { vars := #[186, 214, 285, 133], coeff := #[1, 1, 1, 1], bound := 2, weight := 535715, edges := #[⟨0, 3, 94⟩, ⟨1, 3, 40⟩], triples := #[⟨0, 1, 2⟩] }
def er185_150 : Row := { vars := #[187, 232, 265, 39], coeff := #[1, 1, 1, 1], bound := 2, weight := 428572, edges := #[⟨0, 3, 334⟩, ⟨1, 3, 246⟩], triples := #[⟨0, 1, 2⟩] }
def er185_151 : Row := { vars := #[195, 213, 266, 216, 127], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 660715, edges := #[⟨3, 4, 104⟩, ⟨1, 3, 432⟩, ⟨2, 3, 390⟩, ⟨0, 4, 152⟩, ⟨1, 4, 76⟩], triples := #[⟨0, 1, 2⟩] }
def er185_152 : Row := { vars := #[195, 213, 266, 191, 62], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 339286, edges := #[⟨3, 4, 247⟩, ⟨0, 3, 390⟩, ⟨2, 3, 432⟩, ⟨0, 4, 248⟩, ⟨1, 4, 194⟩], triples := #[⟨0, 1, 2⟩] }
def er185_153 : Row := { vars := #[202, 238, 279, 145, 198], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 77⟩, ⟨0, 3, 92⟩, ⟨2, 3, 135⟩, ⟨0, 4, 400⟩, ⟨1, 4, 508⟩], triples := #[⟨0, 1, 2⟩] }
def er185_154 : Row := { vars := #[202, 241, 287, 146], coeff := #[1, 1, 1, 1], bound := 2, weight := 535715, edges := #[⟨0, 3, 93⟩, ⟨2, 3, 156⟩], triples := #[⟨0, 1, 2⟩] }
def er185_155 : Row := { vars := #[205, 216, 247, 209, 146], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 464286, edges := #[⟨3, 4, 58⟩, ⟨0, 3, 410⟩, ⟨2, 3, 432⟩, ⟨0, 4, 43⟩, ⟨1, 4, 31⟩], triples := #[⟨0, 1, 2⟩] }
def er185_156 : Row := { vars := #[213, 219, 225, 290], coeff := #[1, 1, 1, 1], bound := 2, weight := 428572, edges := #[⟨0, 3, 370⟩, ⟨2, 3, 382⟩], triples := #[⟨0, 1, 2⟩] }
def er185_157 : Row := { vars := #[213, 219, 225, 237, 134], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 571429, edges := #[⟨3, 4, 32⟩, ⟨0, 3, 413⟩, ⟨1, 3, 410⟩, ⟨0, 4, 38⟩, ⟨2, 4, 56⟩], triples := #[⟨0, 1, 2⟩] }
def er185_158 : Row := { vars := #[233, 239, 244, 231, 86], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 139⟩, ⟨1, 3, 454⟩, ⟨2, 3, 448⟩, ⟨0, 4, 136⟩, ⟨2, 4, 154⟩], triples := #[⟨0, 1, 2⟩] }
def er185_159 : Row := { vars := #[250, 262, 291, 254, 122], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 160715, edges := #[⟨3, 4, 58⟩, ⟨0, 3, 464⟩, ⟨2, 3, 486⟩, ⟨0, 4, 43⟩, ⟨1, 4, 30⟩], triples := #[⟨0, 1, 2⟩] }
def er185_160 : Row := { vars := #[250, 271, 282, 128, 254], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 714286, edges := #[⟨3, 4, 22⟩, ⟨0, 3, 7⟩, ⟨2, 3, 66⟩, ⟨0, 4, 464⟩, ⟨1, 4, 508⟩], triples := #[⟨0, 1, 2⟩] }
def er185_161 : Row := { vars := #[257, 262, 272, 232, 3], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 571429, edges := #[⟨3, 4, 300⟩, ⟨1, 3, 382⟩, ⟨2, 3, 370⟩, ⟨0, 4, 257⟩, ⟨1, 4, 267⟩], triples := #[⟨0, 1, 2⟩] }
def er185_162 : Row := { vars := #[259, 265, 270, 237, 48], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 464286, edges := #[⟨3, 4, 231⟩, ⟨0, 3, 381⟩, ⟨1, 3, 369⟩, ⟨0, 4, 332⟩, ⟨2, 4, 334⟩], triples := #[⟨0, 1, 2⟩] }
def er185_163 : Row := { vars := #[276, 282, 292, 215, 128], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 285715, edges := #[⟨3, 4, 74⟩, ⟨1, 3, 383⟩, ⟨2, 3, 371⟩, ⟨0, 4, 41⟩, ⟨1, 4, 66⟩], triples := #[⟨0, 1, 2⟩] }
def er185_164 : Row := { vars := #[4], coeff := #[1], bound := 1, weight := 589286, edges := #[], triples := #[] }
def er185_165 : Row := { vars := #[5], coeff := #[1], bound := 1, weight := 464286, edges := #[], triples := #[] }
def er185_166 : Row := { vars := #[15], coeff := #[1], bound := 1, weight := 750000, edges := #[], triples := #[] }
def er185_167 : Row := { vars := #[16], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er185_168 : Row := { vars := #[19], coeff := #[1], bound := 1, weight := 17858, edges := #[], triples := #[] }
def er185_169 : Row := { vars := #[24], coeff := #[1], bound := 1, weight := 107143, edges := #[], triples := #[] }
def er185_170 : Row := { vars := #[28], coeff := #[1], bound := 1, weight := 428572, edges := #[], triples := #[] }
def er185_171 : Row := { vars := #[29], coeff := #[1], bound := 1, weight := 660715, edges := #[], triples := #[] }
def er185_172 : Row := { vars := #[38], coeff := #[1], bound := 1, weight := 178572, edges := #[], triples := #[] }
def er185_173 : Row := { vars := #[39], coeff := #[1], bound := 1, weight := 517858, edges := #[], triples := #[] }
def er185_174 : Row := { vars := #[42], coeff := #[1], bound := 1, weight := 446429, edges := #[], triples := #[] }
def er185_175 : Row := { vars := #[43], coeff := #[1], bound := 1, weight := 946429, edges := #[], triples := #[] }
def er185_176 : Row := { vars := #[49], coeff := #[1], bound := 1, weight := 357143, edges := #[], triples := #[] }
def er185_177 : Row := { vars := #[50], coeff := #[1], bound := 1, weight := 553572, edges := #[], triples := #[] }
def er185_178 : Row := { vars := #[54], coeff := #[1], bound := 1, weight := 535715, edges := #[], triples := #[] }
def er185_179 : Row := { vars := #[58], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er185_180 : Row := { vars := #[60], coeff := #[1], bound := 1, weight := 17858, edges := #[], triples := #[] }
def er185_181 : Row := { vars := #[63], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er185_182 : Row := { vars := #[79], coeff := #[1], bound := 1, weight := 17858, edges := #[], triples := #[] }
def er185_183 : Row := { vars := #[85], coeff := #[1], bound := 1, weight := 464286, edges := #[], triples := #[] }
def er185_184 : Row := { vars := #[96], coeff := #[1], bound := 1, weight := 89286, edges := #[], triples := #[] }
def er185_185 : Row := { vars := #[98], coeff := #[1], bound := 1, weight := 892858, edges := #[], triples := #[] }
def er185_186 : Row := { vars := #[109], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er185_187 : Row := { vars := #[120], coeff := #[1], bound := 1, weight := 750000, edges := #[], triples := #[] }
def er185_188 : Row := { vars := #[121], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er185_189 : Row := { vars := #[125], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er185_190 : Row := { vars := #[131], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er185_191 : Row := { vars := #[133], coeff := #[1], bound := 1, weight := 357143, edges := #[], triples := #[] }
end HardyCapset20261020.Cert



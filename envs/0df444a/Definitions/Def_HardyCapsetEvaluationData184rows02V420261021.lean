-- Prove2me | Definitions.Def_HardyCapsetEvaluationData184rows02V420261021
-- name    : HardyCapsetEvaluationData184rows02V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:34:24.350053+00:00
-- url     : https://prove2.me/theorems/debac1b9-9983-4df4-86f5-2563867ea280
-- title:
--   HardyCapsetEvaluationData184rows02V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er184_128 : Row := { vars := #[136, 381, 153], coeff := #[1, 1, 1], bound := 1, weight := 710205, edges := #[⟨0, 1, 83⟩, ⟨0, 2, 342⟩, ⟨1, 2, 33⟩], triples := #[] }
def er184_129 : Row := { vars := #[140, 364, 162], coeff := #[1, 1, 1], bound := 1, weight := 289796, edges := #[⟨0, 1, 107⟩, ⟨0, 2, 320⟩, ⟨1, 2, 46⟩], triples := #[] }
def er184_130 : Row := { vars := #[141, 291, 148], coeff := #[1, 1, 1], bound := 1, weight := 289796, edges := #[⟨0, 1, 69⟩, ⟨0, 2, 240⟩, ⟨1, 2, 47⟩], triples := #[] }
def er184_131 : Row := { vars := #[141, 318, 208], coeff := #[1, 1, 1], bound := 1, weight := 710205, edges := #[⟨0, 1, 167⟩, ⟨0, 2, 266⟩, ⟨1, 2, 47⟩], triples := #[] }
def er184_132 : Row := { vars := #[146, 230, 185], coeff := #[1, 1, 1], bound := 1, weight := 693878, edges := #[⟨0, 1, 280⟩, ⟨0, 2, 333⟩, ⟨1, 2, 243⟩], triples := #[] }
def er184_133 : Row := { vars := #[148, 364, 154], coeff := #[1, 1, 1], bound := 1, weight := 710205, edges := #[⟨0, 1, 84⟩, ⟨0, 2, 320⟩, ⟨1, 2, 69⟩], triples := #[] }
def er184_134 : Row := { vars := #[149, 318, 200], coeff := #[1, 1, 1], bound := 1, weight := 289796, edges := #[⟨0, 1, 144⟩, ⟨0, 2, 266⟩, ⟨1, 2, 70⟩], triples := #[] }
def er184_135 : Row := { vars := #[157, 268, 332], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 166⟩, ⟨0, 2, 109⟩, ⟨1, 2, 468⟩], triples := #[] }
def er184_136 : Row := { vars := #[158, 168, 184], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 279⟩, ⟨0, 2, 258⟩, ⟨1, 2, 253⟩], triples := #[] }
def er184_137 : Row := { vars := #[161, 262, 249], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 143⟩, ⟨0, 2, 150⟩, ⟨1, 2, 372⟩], triples := #[] }
def er184_138 : Row := { vars := #[162, 263, 251], coeff := #[1, 1, 1], bound := 1, weight := 710205, edges := #[⟨0, 1, 144⟩, ⟨0, 2, 151⟩, ⟨1, 2, 374⟩], triples := #[] }
def er184_139 : Row := { vars := #[176, 289, 344], coeff := #[1, 1, 1], bound := 1, weight := 693878, edges := #[⟨0, 1, 139⟩, ⟨0, 2, 57⟩, ⟨1, 2, 428⟩], triples := #[] }
def er184_140 : Row := { vars := #[176, 230, 115], coeff := #[1, 1, 1], bound := 1, weight := 306123, edges := #[⟨0, 1, 203⟩, ⟨0, 2, 333⟩, ⟨1, 2, 272⟩], triples := #[] }
def er184_141 : Row := { vars := #[178, 334, 281], coeff := #[1, 1, 1], bound := 1, weight := 295409, edges := #[⟨0, 1, 82⟩, ⟨0, 2, 176⟩, ⟨1, 2, 459⟩], triples := #[] }
def er184_142 : Row := { vars := #[179, 363, 351], coeff := #[1, 1, 1], bound := 1, weight := 524490, edges := #[⟨0, 1, 12⟩, ⟨0, 2, 62⟩, ⟨1, 2, 491⟩], triples := #[] }
def er184_143 : Row := { vars := #[193, 273, 347], coeff := #[1, 1, 1], bound := 1, weight := 732654, edges := #[⟨0, 1, 153⟩, ⟨0, 2, 6⟩, ⟨1, 2, 450⟩], triples := #[] }
def er184_144 : Row := { vars := #[204, 348, 343], coeff := #[1, 1, 1], bound := 1, weight := 732654, edges := #[⟨0, 1, 138⟩, ⟨0, 2, 154⟩, ⟨1, 2, 466⟩], triples := #[] }
def er184_145 : Row := { vars := #[204, 344, 347], coeff := #[1, 1, 1], bound := 1, weight := 267347, edges := #[⟨0, 1, 153⟩, ⟨0, 2, 139⟩, ⟨1, 2, 466⟩], triples := #[] }
def er184_146 : Row := { vars := #[207, 349, 380], coeff := #[1, 1, 1], bound := 1, weight := 36225, edges := #[⟨0, 1, 144⟩, ⟨0, 2, 170⟩, ⟨1, 2, 477⟩], triples := #[] }
def er184_147 : Row := { vars := #[222, 288, 298], coeff := #[1, 1, 1], bound := 1, weight := 231123, edges := #[⟨0, 1, 79⟩, ⟨0, 2, 56⟩, ⟨1, 2, 482⟩], triples := #[] }
def er184_148 : Row := { vars := #[222, 211, 220], coeff := #[1, 1, 1], bound := 1, weight := 359184, edges := #[⟨0, 1, 314⟩, ⟨0, 2, 324⟩, ⟨1, 2, 316⟩], triples := #[] }
def er184_149 : Row := { vars := #[223, 228, 286], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 302⟩, ⟨0, 2, 90⟩, ⟨1, 2, 120⟩], triples := #[] }
def er184_150 : Row := { vars := #[232, 346, 190], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 175⟩, ⟨0, 2, 237⟩, ⟨1, 2, 0⟩], triples := #[] }
def er184_151 : Row := { vars := #[243, 166, 155], coeff := #[1, 1, 1], bound := 1, weight := 493878, edges := #[⟨0, 1, 182⟩, ⟨0, 2, 139⟩, ⟨1, 2, 277⟩], triples := #[] }
def er184_152 : Row := { vars := #[246, 227, 201], coeff := #[1, 1, 1], bound := 1, weight := 360205, edges := #[⟨0, 1, 110⟩, ⟨0, 2, 78⟩, ⟨1, 2, 309⟩], triples := #[] }
def er184_153 : Row := { vars := #[250, 263, 269], coeff := #[1, 1, 1], bound := 1, weight := 289796, edges := #[⟨0, 1, 375⟩, ⟨0, 2, 367⟩, ⟨1, 2, 354⟩], triples := #[] }
def er184_154 : Row := { vars := #[253, 132, 174], coeff := #[1, 1, 1], bound := 1, weight := 526531, edges := #[⟨0, 1, 57⟩, ⟨0, 2, 183⟩, ⟨1, 2, 308⟩], triples := #[] }
def er184_155 : Row := { vars := #[253, 175, 156], coeff := #[1, 1, 1], bound := 1, weight := 316327, edges := #[⟨0, 1, 182⟩, ⟨0, 2, 154⟩, ⟨1, 2, 277⟩], triples := #[] }
def er184_156 : Row := { vars := #[255, 192, 144], coeff := #[1, 1, 1], bound := 1, weight := 941327, edges := #[⟨0, 1, 171⟩, ⟨0, 2, 21⟩, ⟨1, 2, 330⟩], triples := #[] }
def er184_157 : Row := { vars := #[260, 372, 315], coeff := #[1, 1, 1], bound := 1, weight := 271429, edges := #[⟨0, 1, 433⟩, ⟨0, 2, 500⟩, ⟨1, 2, 380⟩], triples := #[] }
def er184_158 : Row := { vars := #[261, 373, 380], coeff := #[1, 1, 1], bound := 1, weight := 197449, edges := #[⟨0, 1, 434⟩, ⟨0, 2, 424⟩, ⟨1, 2, 508⟩], triples := #[] }
def er184_159 : Row := { vars := #[267, 335, 353], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 470⟩, ⟨0, 2, 444⟩, ⟨1, 2, 373⟩], triples := #[] }
def er184_160 : Row := { vars := #[270, 107, 210], coeff := #[1, 1, 1], bound := 1, weight := 947449, edges := #[⟨0, 1, 41⟩, ⟨0, 2, 110⟩, ⟨1, 2, 277⟩], triples := #[] }
def er184_161 : Row := { vars := #[279, 355, 307], coeff := #[1, 1, 1], bound := 1, weight := 186735, edges := #[⟨0, 1, 435⟩, ⟨0, 2, 481⟩, ⟨1, 2, 384⟩], triples := #[] }
def er184_162 : Row := { vars := #[279, 365, 307], coeff := #[1, 1, 1], bound := 1, weight := 523470, edges := #[⟨0, 1, 416⟩, ⟨0, 2, 481⟩, ⟨1, 2, 389⟩], triples := #[] }
def er184_163 : Row := { vars := #[291, 336, 370], coeff := #[1, 1, 1], bound := 1, weight := 710205, edges := #[⟨0, 1, 492⟩, ⟨0, 2, 449⟩, ⟨1, 2, 399⟩], triples := #[] }
def er184_164 : Row := { vars := #[299, 231, 221], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 20⟩, ⟨0, 2, 45⟩, ⟨1, 2, 298⟩], triples := #[] }
def er184_165 : Row := { vars := #[303, 326, 307], coeff := #[1, 1, 1], bound := 1, weight := 132654, edges := #[⟨0, 1, 434⟩, ⟨0, 2, 449⟩, ⟨1, 2, 404⟩], triples := #[] }
def er184_166 : Row := { vars := #[321, 183, 131], coeff := #[1, 1, 1], bound := 1, weight := 795919, edges := #[⟨0, 1, 92⟩, ⟨0, 2, 174⟩, ⟨1, 2, 299⟩], triples := #[] }
def er184_167 : Row := { vars := #[339, 165, 143], coeff := #[1, 1, 1], bound := 1, weight := 585205, edges := #[⟨0, 1, 92⟩, ⟨0, 2, 186⟩, ⟨1, 2, 298⟩], triples := #[] }
def er184_168 : Row := { vars := #[349, 365, 380], coeff := #[1, 1, 1], bound := 1, weight := 476531, edges := #[⟨0, 1, 492⟩, ⟨0, 2, 477⟩, ⟨1, 2, 458⟩], triples := #[] }
def er184_169 : Row := { vars := #[358, 237, 132], coeff := #[1, 1, 1], bound := 1, weight := 473470, edges := #[⟨0, 1, 137⟩, ⟨0, 2, 114⟩, ⟨1, 2, 245⟩], triples := #[] }
def er184_170 : Row := { vars := #[360, 175, 156], coeff := #[1, 1, 1], bound := 1, weight := 683674, edges := #[⟨0, 1, 7⟩, ⟨0, 2, 55⟩, ⟨1, 2, 277⟩], triples := #[] }
def er184_171 : Row := { vars := #[373, 381, 380], coeff := #[1, 1, 1], bound := 1, weight := 289796, edges := #[⟨0, 1, 511⟩, ⟨0, 2, 508⟩, ⟨1, 2, 501⟩], triples := #[] }
def er184_172 : Row := { vars := #[0, 49, 86, 1, 20], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 3572, edges := #[⟨3, 4, 36⟩, ⟨1, 3, 165⟩, ⟨2, 3, 77⟩, ⟨0, 4, 44⟩, ⟨2, 4, 129⟩], triples := #[⟨0, 1, 2⟩] }
def er184_173 : Row := { vars := #[0, 160, 340, 73, 98], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 290817, edges := #[⟨3, 4, 174⟩, ⟨0, 3, 105⟩, ⟨2, 3, 301⟩, ⟨0, 4, 110⟩, ⟨1, 4, 392⟩], triples := #[⟨0, 1, 2⟩] }
def er184_174 : Row := { vars := #[0, 160, 340, 21], coeff := #[1, 1, 1, 1], bound := 2, weight := 38776, edges := #[⟨0, 3, 42⟩, ⟨1, 3, 503⟩], triples := #[⟨0, 1, 2⟩] }
def er184_175 : Row := { vars := #[1, 145, 274, 319, 99], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 236735, edges := #[⟨3, 4, 223⟩, ⟨0, 3, 333⟩, ⟨1, 3, 167⟩, ⟨0, 4, 109⟩, ⟨2, 4, 250⟩], triples := #[⟨0, 1, 2⟩] }
def er184_176 : Row := { vars := #[1, 203, 296, 86, 88], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 493878, edges := #[⟨3, 4, 158⟩, ⟨0, 3, 77⟩, ⟨1, 3, 465⟩, ⟨0, 4, 72⟩, ⟨2, 4, 210⟩], triples := #[⟨0, 1, 2⟩] }
def er184_177 : Row := { vars := #[2, 4, 37, 3, 81], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 58674, edges := #[⟨3, 4, 73⟩, ⟨1, 3, 58⟩, ⟨2, 3, 12⟩, ⟨0, 4, 81⟩, ⟨1, 4, 128⟩], triples := #[⟨0, 1, 2⟩] }
def er184_178 : Row := { vars := #[2, 130, 287, 214, 69], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 693878, edges := #[⟨3, 4, 367⟩, ⟨0, 3, 438⟩, ⟨2, 3, 94⟩, ⟨0, 4, 171⟩, ⟨1, 4, 466⟩], triples := #[⟨0, 1, 2⟩] }
def er184_179 : Row := { vars := #[2, 142, 275, 112, 14], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 399⟩, ⟨0, 3, 355⟩, ⟨2, 3, 57⟩, ⟨0, 4, 44⟩, ⟨1, 4, 376⟩], triples := #[⟨0, 1, 2⟩] }
def er184_180 : Row := { vars := #[3, 46, 80, 2, 96], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 20409, edges := #[⟨3, 4, 110⟩, ⟨1, 3, 152⟩, ⟨2, 3, 82⟩, ⟨0, 4, 108⟩, ⟨2, 4, 174⟩], triples := #[⟨0, 1, 2⟩] }
def er184_181 : Row := { vars := #[3, 139, 278, 250, 34], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 559184, edges := #[⟨3, 4, 233⟩, ⟨0, 3, 201⟩, ⟨1, 3, 11⟩, ⟨0, 4, 0⟩, ⟨2, 4, 208⟩], triples := #[⟨0, 1, 2⟩] }
def er184_182 : Row := { vars := #[3, 197, 300, 251, 81], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 138776, edges := #[⟨3, 4, 253⟩, ⟨0, 3, 200⟩, ⟨1, 3, 83⟩, ⟨0, 4, 73⟩, ⟨2, 4, 211⟩], triples := #[⟨0, 1, 2⟩] }
def er184_183 : Row := { vars := #[6, 117, 292, 301], coeff := #[1, 1, 1, 1], bound := 2, weight := 269388, edges := #[⟨0, 3, 347⟩, ⟨1, 3, 140⟩], triples := #[⟨0, 1, 2⟩] }
def er184_184 : Row := { vars := #[8, 144, 264, 199, 65], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 58674, edges := #[⟨3, 4, 402⟩, ⟨0, 3, 438⟩, ⟨2, 3, 94⟩, ⟨1, 4, 463⟩, ⟨2, 4, 331⟩], triples := #[⟨0, 1, 2⟩] }
def er184_185 : Row := { vars := #[10, 159, 374, 207], coeff := #[1, 1, 1, 1], bound := 2, weight := 963776, edges := #[⟨0, 3, 446⟩, ⟨2, 3, 169⟩], triples := #[⟨0, 1, 2⟩] }
def er184_186 : Row := { vars := #[11, 110, 293, 285, 19], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 441327, edges := #[⟨3, 4, 210⟩, ⟨0, 3, 196⟩, ⟨1, 3, 33⟩, ⟨1, 4, 395⟩, ⟨2, 4, 221⟩], triples := #[⟨0, 1, 2⟩] }
def er184_187 : Row := { vars := #[11, 110, 293, 343, 67], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 148980, edges := #[⟨3, 4, 240⟩, ⟨0, 3, 279⟩, ⟨1, 3, 107⟩, ⟨1, 4, 491⟩, ⟨2, 4, 307⟩], triples := #[⟨0, 1, 2⟩] }
def er184_188 : Row := { vars := #[12, 139, 264, 120, 53], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 289796, edges := #[⟨3, 4, 459⟩, ⟨0, 3, 396⟩, ⟨1, 3, 228⟩, ⟨0, 4, 186⟩, ⟨2, 4, 299⟩], triples := #[⟨0, 1, 2⟩] }
def er184_189 : Row := { vars := #[17, 121, 282, 213, 165], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 414796, edges := #[⟨3, 4, 224⟩, ⟨1, 3, 280⟩, ⟨2, 3, 79⟩, ⟨1, 4, 336⟩, ⟨2, 4, 140⟩], triples := #[⟨0, 1, 2⟩] }
def er184_190 : Row := { vars := #[21, 180, 350, 114], coeff := #[1, 1, 1, 1], bound := 2, weight := 518878, edges := #[⟨0, 3, 394⟩, ⟨1, 3, 324⟩], triples := #[⟨0, 1, 2⟩] }
def er184_191 : Row := { vars := #[22, 226, 304, 326], coeff := #[1, 1, 1, 1], bound := 2, weight := 867347, edges := #[⟨1, 3, 37⟩, ⟨2, 3, 433⟩], triples := #[⟨0, 1, 2⟩] }
end HardyCapset20261020.Cert



-- Prove2me | Definitions.Def_HardyCapsetEvaluationData178rows02V420261021
-- name    : HardyCapsetEvaluationData178rows02V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:16:27.125387+00:00
-- url     : https://prove2.me/theorems/446330f1-4007-4397-b358-7306ab8c5354
-- title:
--   HardyCapsetEvaluationData178rows02V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er178_128 : Row := { vars := #[159, 263, 354], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 29⟩, ⟨0, 2, 111⟩, ⟨1, 2, 411⟩], triples := #[] }
def er178_129 : Row := { vars := #[162, 277, 323], coeff := #[1, 1, 1], bound := 1, weight := 997462, edges := #[⟨0, 1, 33⟩, ⟨0, 2, 169⟩, ⟨1, 2, 458⟩], triples := #[] }
def er178_130 : Row := { vars := #[165, 334, 380], coeff := #[1, 1, 1], bound := 1, weight := 2539, edges := #[⟨0, 1, 147⟩, ⟨0, 2, 123⟩, ⟨1, 2, 369⟩], triples := #[] }
def er178_131 : Row := { vars := #[166, 333, 211], coeff := #[1, 1, 1], bound := 1, weight := 724965, edges := #[⟨0, 1, 147⟩, ⟨0, 2, 263⟩, ⟨1, 2, 70⟩], triples := #[] }
def er178_132 : Row := { vars := #[167, 278, 360], coeff := #[1, 1, 1], bound := 1, weight := 219747, edges := #[⟨0, 1, 29⟩, ⟨0, 2, 111⟩, ⟨1, 2, 407⟩], triples := #[] }
def er178_133 : Row := { vars := #[168, 325, 269], coeff := #[1, 1, 1], bound := 1, weight := 367560, edges := #[⟨0, 1, 178⟩, ⟨0, 2, 15⟩, ⟨1, 2, 459⟩], triples := #[] }
def er178_134 : Row := { vars := #[173, 372, 340], coeff := #[1, 1, 1], bound := 1, weight := 264881, edges := #[⟨0, 1, 69⟩, ⟨0, 2, 110⟩, ⟨1, 2, 383⟩], triples := #[] }
def er178_135 : Row := { vars := #[176, 254, 286], coeff := #[1, 1, 1], bound := 1, weight := 261213, edges := #[⟨0, 1, 165⟩, ⟨0, 2, 191⟩, ⟨1, 2, 394⟩], triples := #[] }
def er178_136 : Row := { vars := #[184, 256, 353], coeff := #[1, 1, 1], bound := 1, weight := 910015, edges := #[⟨0, 1, 181⟩, ⟨0, 2, 50⟩, ⟨1, 2, 404⟩], triples := #[] }
def er178_137 : Row := { vars := #[189, 268, 310], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 180⟩, ⟨0, 2, 167⟩, ⟨1, 2, 384⟩], triples := #[] }
def er178_138 : Row := { vars := #[191, 358, 299], coeff := #[1, 1, 1], bound := 1, weight := 910015, edges := #[⟨0, 1, 39⟩, ⟨0, 2, 154⟩, ⟨1, 2, 429⟩], triples := #[] }
def er178_139 : Row := { vars := #[192, 233, 111], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 205⟩, ⟨0, 2, 334⟩, ⟨1, 2, 255⟩], triples := #[] }
def er178_140 : Row := { vars := #[202, 224, 352], coeff := #[1, 1, 1], bound := 1, weight := 185050, edges := #[⟨0, 1, 195⟩, ⟨0, 2, 21⟩, ⟨1, 2, 191⟩], triples := #[] }
def er178_141 : Row := { vars := #[203, 224, 110], coeff := #[1, 1, 1], bound := 1, weight := 380254, edges := #[⟨0, 1, 193⟩, ⟨0, 2, 312⟩, ⟨1, 2, 296⟩], triples := #[] }
def er178_142 : Row := { vars := #[204, 351, 116], coeff := #[1, 1, 1], bound := 1, weight := 513964, edges := #[⟨0, 1, 20⟩, ⟨0, 2, 310⟩, ⟨1, 2, 100⟩], triples := #[] }
def er178_143 : Row := { vars := #[204, 170, 190], coeff := #[1, 1, 1], bound := 1, weight := 95064, edges := #[⟨0, 1, 262⟩, ⟨0, 2, 252⟩, ⟨1, 2, 283⟩], triples := #[] }
def er178_144 : Row := { vars := #[213, 129, 291], coeff := #[1, 1, 1], bound := 1, weight := 910015, edges := #[⟨0, 1, 246⟩, ⟨0, 2, 125⟩, ⟨1, 2, 37⟩], triples := #[] }
def er178_145 : Row := { vars := #[213, 253, 286], coeff := #[1, 1, 1], bound := 1, weight := 89986, edges := #[⟨0, 1, 105⟩, ⟨0, 2, 131⟩, ⟨1, 2, 395⟩], triples := #[] }
def er178_146 : Row := { vars := #[218, 346, 249], coeff := #[1, 1, 1], bound := 1, weight := 457546, edges := #[⟨0, 1, 13⟩, ⟨0, 2, 88⟩, ⟨1, 2, 481⟩], triples := #[] }
def er178_147 : Row := { vars := #[221, 256, 316], coeff := #[1, 1, 1], bound := 1, weight := 89986, edges := #[⟨0, 1, 121⟩, ⟨0, 2, 49⟩, ⟨1, 2, 458⟩], triples := #[] }
def er178_148 : Row := { vars := #[228, 321, 238], coeff := #[1, 1, 1], bound := 1, weight := 113400, edges := #[⟨0, 1, 39⟩, ⟨0, 2, 306⟩, ⟨1, 2, 0⟩], triples := #[] }
def er178_149 : Row := { vars := #[228, 119, 201], coeff := #[1, 1, 1], bound := 1, weight := 495628, edges := #[⟨0, 1, 278⟩, ⟨0, 2, 216⟩, ⟨1, 2, 309⟩], triples := #[] }
def er178_150 : Row := { vars := #[230, 320, 197], coeff := #[1, 1, 1], bound := 1, weight := 275036, edges := #[⟨0, 1, 38⟩, ⟨0, 2, 200⟩, ⟨1, 2, 119⟩], triples := #[] }
def er178_151 : Row := { vars := #[230, 197, 116], coeff := #[1, 1, 1], bound := 1, weight := 486037, edges := #[⟨0, 1, 200⟩, ⟨0, 2, 278⟩, ⟨1, 2, 329⟩], triples := #[] }
def er178_152 : Row := { vars := #[230, 298, 185], coeff := #[1, 1, 1], bound := 1, weight := 238929, edges := #[⟨0, 1, 93⟩, ⟨0, 2, 229⟩, ⟨1, 2, 133⟩], triples := #[] }
def er178_153 : Row := { vars := #[232, 253, 286], coeff := #[1, 1, 1], bound := 1, weight := 648802, edges := #[⟨0, 1, 108⟩, ⟨0, 2, 86⟩, ⟨1, 2, 395⟩], triples := #[] }
def er178_154 : Row := { vars := #[239, 118, 190], coeff := #[1, 1, 1], bound := 1, weight := 814951, edges := #[⟨0, 1, 256⟩, ⟨0, 2, 218⟩, ⟨1, 2, 330⟩], triples := #[] }
def er178_155 : Row := { vars := #[240, 290, 186], coeff := #[1, 1, 1], bound := 1, weight := 185050, edges := #[⟨0, 1, 75⟩, ⟨0, 2, 201⟩, ⟨1, 2, 178⟩], triples := #[] }
def er178_156 : Row := { vars := #[240, 185, 284], coeff := #[1, 1, 1], bound := 1, weight := 724965, edges := #[⟨0, 1, 204⟩, ⟨0, 2, 93⟩, ⟨1, 2, 169⟩], triples := #[] }
def er178_157 : Row := { vars := #[241, 109, 187], coeff := #[1, 1, 1], bound := 1, weight := 820029, edges := #[⟨0, 1, 258⟩, ⟨0, 2, 192⟩, ⟨1, 2, 351⟩], triples := #[] }
def er178_158 : Row := { vars := #[244, 208, 155], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 76⟩, ⟨0, 2, 8⟩, ⟨1, 2, 254⟩], triples := #[] }
def er178_159 : Row := { vars := #[249, 383, 336], coeff := #[1, 1, 1], bound := 1, weight := 460085, edges := #[⟨0, 1, 427⟩, ⟨0, 2, 497⟩, ⟨1, 2, 356⟩], triples := #[] }
def er178_160 : Row := { vars := #[250, 345, 373], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 481⟩, ⟨0, 2, 442⟩, ⟨1, 2, 357⟩], triples := #[] }
def er178_161 : Row := { vars := #[251, 334, 384], coeff := #[1, 1, 1], bound := 1, weight := 675600, edges := #[⟨0, 1, 503⟩, ⟨0, 2, 420⟩, ⟨1, 2, 358⟩], triples := #[] }
def er178_162 : Row := { vars := #[251, 371, 347], coeff := #[1, 1, 1], bound := 1, weight := 324401, edges := #[⟨0, 1, 449⟩, ⟨0, 2, 474⟩, ⟨1, 2, 358⟩], triples := #[] }
def er178_163 : Row := { vars := #[252, 333, 384], coeff := #[1, 1, 1], bound := 1, weight := 7617, edges := #[⟨0, 1, 503⟩, ⟨0, 2, 419⟩, ⟨1, 2, 359⟩], triples := #[] }
def er178_164 : Row := { vars := #[258, 163, 212], coeff := #[1, 1, 1], bound := 1, weight := 185050, edges := #[⟨0, 1, 8⟩, ⟨0, 2, 94⟩, ⟨1, 2, 254⟩], triples := #[] }
def er178_165 : Row := { vars := #[258, 145, 178], coeff := #[1, 1, 1], bound := 1, weight := 460085, edges := #[⟨0, 1, 56⟩, ⟨0, 2, 141⟩, ⟨1, 2, 331⟩], triples := #[] }
def er178_166 : Row := { vars := #[260, 148, 212], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 44⟩, ⟨0, 2, 93⟩, ⟨1, 2, 276⟩], triples := #[] }
def er178_167 : Row := { vars := #[278, 207, 156], coeff := #[1, 1, 1], bound := 1, weight := 5078, edges := #[⟨0, 1, 92⟩, ⟨0, 2, 17⟩, ⟨1, 2, 255⟩], triples := #[] }
def er178_168 : Row := { vars := #[288, 117, 178], coeff := #[1, 1, 1], bound := 1, weight := 416644, edges := #[⟨0, 1, 56⟩, ⟨0, 2, 183⟩, ⟨1, 2, 299⟩], triples := #[] }
def er178_169 : Row := { vars := #[297, 112, 170], coeff := #[1, 1, 1], bound := 1, weight := 814951, edges := #[⟨0, 1, 2⟩, ⟨0, 2, 171⟩, ⟨1, 2, 298⟩], triples := #[] }
def er178_170 : Row := { vars := #[303, 119, 178], coeff := #[1, 1, 1], bound := 1, weight := 123273, edges := #[⟨0, 1, 20⟩, ⟨0, 2, 171⟩, ⟨1, 2, 298⟩], triples := #[] }
def er178_171 : Row := { vars := #[303, 187, 130], coeff := #[1, 1, 1], bound := 1, weight := 786742, edges := #[⟨0, 1, 154⟩, ⟨0, 2, 8⟩, ⟨1, 2, 330⟩], triples := #[] }
def er178_172 : Row := { vars := #[307, 131, 175], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 4⟩, ⟨0, 2, 172⟩, ⟨1, 2, 299⟩], triples := #[] }
def er178_173 : Row := { vars := #[312, 234, 106], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 2⟩, ⟨0, 2, 141⟩, ⟨1, 2, 255⟩], triples := #[] }
def er178_174 : Row := { vars := #[326, 105, 156], coeff := #[1, 1, 1], bound := 1, weight := 89986, edges := #[⟨0, 1, 152⟩, ⟨0, 2, 173⟩, ⟨1, 2, 224⟩], triples := #[] }
def er178_175 : Row := { vars := #[329, 332, 333], coeff := #[1, 1, 1], bound := 1, weight := 267419, edges := #[⟨0, 1, 433⟩, ⟨0, 2, 432⟩, ⟨1, 2, 426⟩], triples := #[] }
def er178_176 : Row := { vars := #[329, 332, 372], coeff := #[1, 1, 1], bound := 1, weight := 269958, edges := #[⟨0, 1, 433⟩, ⟨0, 2, 393⟩, ⟨1, 2, 390⟩], triples := #[] }
def er178_177 : Row := { vars := #[336, 381, 343], coeff := #[1, 1, 1], bound := 1, weight := 539916, edges := #[⟨0, 1, 358⟩, ⟨0, 2, 404⟩, ⟨1, 2, 400⟩], triples := #[] }
def er178_178 : Row := { vars := #[340, 343, 370], coeff := #[1, 1, 1], bound := 1, weight := 457546, edges := #[⟨0, 1, 456⟩, ⟨0, 2, 380⟩, ⟨1, 2, 368⟩], triples := #[] }
def er178_179 : Row := { vars := #[355, 119, 148], coeff := #[1, 1, 1], bound := 1, weight := 170099, edges := #[⟨0, 1, 93⟩, ⟨0, 2, 122⟩, ⟨1, 2, 234⟩], triples := #[] }
def er178_180 : Row := { vars := #[363, 104, 141], coeff := #[1, 1, 1], bound := 1, weight := 5078, edges := #[⟨0, 1, 92⟩, ⟨0, 2, 125⟩, ⟨1, 2, 235⟩], triples := #[] }
def er178_181 : Row := { vars := #[366, 371, 369], coeff := #[1, 1, 1], bound := 1, weight := 675600, edges := #[⟨0, 1, 486⟩, ⟨0, 2, 488⟩, ⟨1, 2, 480⟩], triples := #[] }
def er178_182 : Row := { vars := #[0, 152, 297, 90], coeff := #[1, 1, 1, 1], bound := 2, weight := 185050, edges := #[⟨0, 3, 76⟩, ⟨1, 3, 449⟩], triples := #[⟨0, 1, 2⟩] }
def er178_183 : Row := { vars := #[0, 180, 349, 72, 40], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 195205, edges := #[⟨3, 4, 113⟩, ⟨0, 3, 105⟩, ⟨2, 3, 300⟩, ⟨0, 4, 8⟩, ⟨1, 4, 485⟩], triples := #[⟨0, 1, 2⟩] }
def er178_184 : Row := { vars := #[0, 180, 349, 110, 71], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 619747, edges := #[⟨3, 4, 473⟩, ⟨0, 3, 374⟩, ⟨2, 3, 76⟩, ⟨0, 4, 171⟩, ⟨1, 4, 431⟩], triples := #[⟨0, 1, 2⟩] }
def er178_185 : Row := { vars := #[1, 23, 24, 31], coeff := #[1, 1, 1, 1], bound := 2, weight := 95064, edges := #[⟨0, 3, 35⟩, ⟨2, 3, 40⟩], triples := #[⟨0, 1, 2⟩] }
def er178_186 : Row := { vars := #[1, 214, 313, 86, 40], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 624824, edges := #[⟨3, 4, 119⟩, ⟨0, 3, 74⟩, ⟨1, 3, 465⟩, ⟨0, 4, 0⟩, ⟨2, 4, 319⟩], triples := #[⟨0, 1, 2⟩] }
def er178_187 : Row := { vars := #[2, 45, 83, 46], coeff := #[1, 1, 1, 1], bound := 2, weight := 89986, edges := #[⟨0, 3, 152⟩, ⟨1, 3, 85⟩], triples := #[⟨0, 1, 2⟩] }
def er178_188 : Row := { vars := #[2, 172, 355, 80, 65], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 447391, edges := #[⟨3, 4, 53⟩, ⟨0, 3, 85⟩, ⟨2, 3, 302⟩, ⟨0, 4, 183⟩, ⟨1, 4, 451⟩], triples := #[⟨0, 1, 2⟩] }
def er178_189 : Row := { vars := #[3, 46, 80, 2, 65], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 44288, edges := #[⟨3, 4, 183⟩, ⟨1, 3, 152⟩, ⟨2, 3, 85⟩, ⟨0, 4, 181⟩, ⟨2, 4, 53⟩], triples := #[⟨0, 1, 2⟩] }
def er178_190 : Row := { vars := #[3, 139, 306, 5, 81], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 130⟩, ⟨0, 3, 58⟩, ⟨1, 3, 387⟩, ⟨0, 4, 73⟩, ⟨2, 4, 264⟩], triples := #[⟨0, 1, 2⟩] }
def er178_191 : Row := { vars := #[3, 169, 356, 365, 13], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 274⟩, ⟨0, 3, 280⟩, ⟨1, 3, 49⟩, ⟨0, 4, 37⟩, ⟨2, 4, 285⟩], triples := #[⟨0, 1, 2⟩] }
end HardyCapset20261020.Cert



-- Prove2me | Definitions.Def_HardyCapsetEvaluationData184rows03V420261021
-- name    : HardyCapsetEvaluationData184rows03V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:34:36.127045+00:00
-- url     : https://prove2.me/theorems/b6f7af31-8df0-4b0e-a53d-19a0c34c3216
-- title:
--   HardyCapsetEvaluationData184rows03V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er184_192 : Row := { vars := #[23, 139, 259, 372, 251], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 151021, edges := #[⟨3, 4, 415⟩, ⟨1, 3, 120⟩, ⟨2, 3, 434⟩, ⟨1, 4, 10⟩, ⟨2, 4, 372⟩], triples := #[⟨0, 1, 2⟩] }
def er184_193 : Row := { vars := #[23, 205, 337, 227], coeff := #[1, 1, 1, 1], bound := 2, weight := 143368, edges := #[⟨1, 3, 315⟩, ⟨2, 3, 58⟩], triples := #[⟨0, 1, 2⟩] }
def er184_194 : Row := { vars := #[26, 119, 280, 302], coeff := #[1, 1, 1, 1], bound := 2, weight := 197449, edges := #[⟨0, 3, 324⟩, ⟨1, 3, 141⟩], triples := #[⟨0, 1, 2⟩] }
def er184_195 : Row := { vars := #[26, 172, 350, 362], coeff := #[1, 1, 1, 1], bound := 2, weight := 802552, edges := #[⟨1, 3, 0⟩, ⟨2, 3, 501⟩], triples := #[⟨0, 1, 2⟩] }
def er184_196 : Row := { vars := #[29, 135, 256, 370], coeff := #[1, 1, 1, 1], bound := 2, weight := 289796, edges := #[⟨0, 3, 276⟩, ⟨2, 3, 433⟩], triples := #[⟨0, 1, 2⟩] }
def er184_197 : Row := { vars := #[31, 110, 281, 298, 99], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 446429, edges := #[⟨3, 4, 230⟩, ⟨0, 3, 311⟩, ⟨1, 3, 166⟩, ⟨1, 4, 415⟩, ⟨2, 4, 253⟩], triples := #[⟨0, 1, 2⟩] }
def er184_198 : Row := { vars := #[31, 225, 304, 25], coeff := #[1, 1, 1, 1], bound := 2, weight := 553572, edges := #[⟨0, 3, 43⟩, ⟨2, 3, 325⟩], triples := #[⟨0, 1, 2⟩] }
def er184_199 : Row := { vars := #[32, 127, 264, 120, 64], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 387756, edges := #[⟨3, 4, 490⟩, ⟨0, 3, 386⟩, ⟨1, 3, 238⟩, ⟨0, 4, 151⟩, ⟨2, 4, 330⟩], triples := #[⟨0, 1, 2⟩] }
def er184_200 : Row := { vars := #[35, 205, 306, 154], coeff := #[1, 1, 1, 1], bound := 2, weight := 289796, edges := #[⟨0, 3, 488⟩, ⟨2, 3, 121⟩], triples := #[⟨0, 1, 2⟩] }
def er184_201 : Row := { vars := #[37, 120, 271, 32, 69], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 306123, edges := #[⟨3, 4, 187⟩, ⟨0, 3, 58⟩, ⟨1, 3, 386⟩, ⟨1, 4, 469⟩, ⟨2, 4, 307⟩], triples := #[⟨0, 1, 2⟩] }
def er184_202 : Row := { vars := #[37, 120, 271, 3, 97], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 635205, edges := #[⟨3, 4, 109⟩, ⟨0, 3, 12⟩, ⟨2, 3, 238⟩, ⟨1, 4, 415⟩, ⟨2, 4, 253⟩], triples := #[⟨0, 1, 2⟩] }
def er184_203 : Row := { vars := #[41, 103, 280, 315], coeff := #[1, 1, 1, 1], bound := 2, weight := 151021, edges := #[⟨0, 3, 299⟩, ⟨2, 3, 478⟩], triples := #[⟨0, 1, 2⟩] }
def er184_204 : Row := { vars := #[41, 163, 350, 298], coeff := #[1, 1, 1, 1], bound := 2, weight := 322449, edges := #[⟨0, 3, 314⟩, ⟨1, 3, 123⟩], triples := #[⟨0, 1, 2⟩] }
def er184_205 : Row := { vars := #[43, 131, 257, 136, 40], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 138776, edges := #[⟨3, 4, 379⟩, ⟨0, 3, 375⟩, ⟨2, 3, 42⟩, ⟨1, 4, 364⟩, ⟨2, 4, 224⟩], triples := #[⟨0, 1, 2⟩] }
def er184_206 : Row := { vars := #[43, 159, 368, 361], coeff := #[1, 1, 1, 1], bound := 2, weight := 36225, edges := #[⟨0, 3, 244⟩, ⟨2, 3, 470⟩], triples := #[⟨0, 1, 2⟩] }
def er184_207 : Row := { vars := #[45, 203, 257, 110, 66], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 506123, edges := #[⟨3, 4, 490⟩, ⟨0, 3, 465⟩, ⟨1, 3, 247⟩, ⟨0, 4, 126⟩, ⟨2, 4, 330⟩], triples := #[⟨0, 1, 2⟩] }
def er184_208 : Row := { vars := #[51, 205, 253, 307], coeff := #[1, 1, 1, 1], bound := 2, weight := 157143, edges := #[⟨0, 3, 277⟩, ⟨2, 3, 511⟩], triples := #[⟨0, 1, 2⟩] }
def er184_209 : Row := { vars := #[57, 135, 369, 269], coeff := #[1, 1, 1, 1], bound := 2, weight := 236735, edges := #[⟨0, 3, 299⟩, ⟨2, 3, 423⟩], triples := #[⟨0, 1, 2⟩] }
def er184_210 : Row := { vars := #[58, 110, 340, 257, 66], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 441327, edges := #[⟨3, 4, 330⟩, ⟨0, 3, 301⟩, ⟨2, 3, 411⟩, ⟨0, 4, 128⟩, ⟨1, 4, 490⟩], triples := #[⟨0, 1, 2⟩] }
def er184_211 : Row := { vars := #[61, 197, 259, 324, 310], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 387756, edges := #[⟨3, 4, 404⟩, ⟨1, 3, 11⟩, ⟨2, 3, 481⟩, ⟨1, 4, 36⟩, ⟨2, 4, 509⟩], triples := #[⟨0, 1, 2⟩] }
def er184_212 : Row := { vars := #[61, 201, 257, 208, 59], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 122449, edges := #[⟨3, 4, 376⟩, ⟨0, 3, 372⟩, ⟨2, 3, 78⟩, ⟨1, 4, 367⟩, ⟨2, 4, 299⟩], triples := #[⟨0, 1, 2⟩] }
def er184_213 : Row := { vars := #[62, 209, 292, 333], coeff := #[1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨0, 3, 254⟩, ⟨2, 3, 501⟩], triples := #[⟨0, 1, 2⟩] }
def er184_214 : Row := { vars := #[75, 119, 304, 277], coeff := #[1, 1, 1, 1], bound := 2, weight := 327041, edges := #[⟨0, 3, 292⟩, ⟨1, 3, 45⟩], triples := #[⟨0, 1, 2⟩] }
def er184_215 : Row := { vars := #[77, 178, 292, 73], coeff := #[1, 1, 1, 1], bound := 2, weight := 203062, edges := #[⟨0, 3, 137⟩, ⟨2, 3, 270⟩], triples := #[⟨0, 1, 2⟩] }
def er184_216 : Row := { vars := #[78, 147, 311, 248], coeff := #[1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨0, 3, 244⟩, ⟨2, 3, 511⟩], triples := #[⟨0, 1, 2⟩] }
def er184_217 : Row := { vars := #[80, 151, 264, 120, 96], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 979592, edges := #[⟨3, 4, 414⟩, ⟨0, 3, 406⟩, ⟨1, 3, 302⟩, ⟨0, 4, 174⟩, ⟨2, 4, 254⟩], triples := #[⟨0, 1, 2⟩] }
def er184_218 : Row := { vars := #[83, 120, 295, 302, 81], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 620919, edges := #[⟨3, 4, 209⟩, ⟨0, 3, 201⟩, ⟨1, 3, 143⟩, ⟨1, 4, 405⟩, ⟨2, 4, 223⟩], triples := #[⟨0, 1, 2⟩] }
def er184_219 : Row := { vars := #[83, 121, 294, 108, 181], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 240307, edges := #[⟨3, 4, 308⟩, ⟨1, 3, 201⟩, ⟨2, 3, 138⟩, ⟨1, 4, 315⟩, ⟨2, 4, 111⟩], triples := #[⟨0, 1, 2⟩] }
def er184_220 : Row := { vars := #[86, 110, 294, 257, 71], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 265817, edges := #[⟨3, 4, 309⟩, ⟨0, 3, 247⟩, ⟨2, 3, 465⟩, ⟨0, 4, 27⟩, ⟨1, 4, 469⟩], triples := #[⟨0, 1, 2⟩] }
def er184_221 : Row := { vars := #[89, 151, 259, 149, 363], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 20409, edges := #[⟨3, 4, 80⟩, ⟨0, 3, 427⟩, ⟨2, 3, 10⟩, ⟨0, 4, 331⟩, ⟨2, 4, 445⟩], triples := #[⟨0, 1, 2⟩] }
def er184_222 : Row := { vars := #[89, 155, 257, 149, 94], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 506123, edges := #[⟨3, 4, 412⟩, ⟨0, 3, 427⟩, ⟨2, 3, 5⟩, ⟨1, 4, 399⟩, ⟨2, 4, 276⟩], triples := #[⟨0, 1, 2⟩] }
def er184_223 : Row := { vars := #[91, 180, 280, 308], coeff := #[1, 1, 1, 1], bound := 2, weight := 422449, edges := #[⟨1, 3, 73⟩, ⟨2, 3, 488⟩], triples := #[⟨0, 1, 2⟩] }
def er184_224 : Row := { vars := #[121, 124, 125, 344, 114], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 38776, edges := #[⟨3, 4, 99⟩, ⟨0, 3, 93⟩, ⟨2, 3, 94⟩, ⟨0, 4, 197⟩, ⟨2, 4, 199⟩], triples := #[⟨0, 1, 2⟩] }
def er184_225 : Row := { vars := #[121, 134, 146, 214, 173], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 306123, edges := #[⟨3, 4, 225⟩, ⟨0, 3, 279⟩, ⟨1, 3, 257⟩, ⟨0, 4, 347⟩, ⟨1, 4, 325⟩], triples := #[⟨0, 1, 2⟩] }
def er184_226 : Row := { vars := #[135, 188, 197, 174], coeff := #[1, 1, 1, 1], bound := 2, weight := 473470, edges := #[⟨0, 3, 323⟩, ⟨1, 3, 247⟩], triples := #[⟨0, 1, 2⟩] }
def er184_227 : Row := { vars := #[205, 222, 239, 211, 220], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 341837, edges := #[⟨3, 4, 316⟩, ⟨0, 3, 337⟩, ⟨1, 3, 314⟩, ⟨0, 4, 347⟩, ⟨1, 4, 324⟩], triples := #[⟨0, 1, 2⟩] }
def er184_228 : Row := { vars := #[205, 222, 239, 229, 238], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 67858, edges := #[⟨3, 4, 338⟩, ⟨0, 3, 314⟩, ⟨2, 3, 337⟩, ⟨0, 4, 324⟩, ⟨2, 4, 347⟩], triples := #[⟨0, 1, 2⟩] }
def er184_229 : Row := { vars := #[259, 260, 261, 136, 250], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 151021, edges := #[⟨3, 4, 54⟩, ⟨0, 3, 47⟩, ⟨1, 3, 46⟩, ⟨0, 4, 373⟩, ⟨1, 4, 372⟩], triples := #[⟨0, 1, 2⟩] }
def er184_230 : Row := { vars := #[259, 303, 349, 153, 336], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 289796, edges := #[⟨3, 4, 115⟩, ⟨0, 3, 167⟩, ⟨1, 3, 107⟩, ⟨0, 4, 470⟩, ⟨1, 4, 416⟩], triples := #[⟨0, 1, 2⟩] }
def er184_231 : Row := { vars := #[260, 303, 350, 315, 308], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 577552, edges := #[⟨3, 4, 432⟩, ⟨0, 3, 500⟩, ⟨1, 3, 447⟩, ⟨0, 4, 510⟩, ⟨1, 4, 457⟩], triples := #[⟨0, 1, 2⟩] }
def er184_232 : Row := { vars := #[261, 304, 349, 362, 355], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 119388, edges := #[⟨3, 4, 486⟩, ⟨0, 3, 447⟩, ⟨2, 3, 500⟩, ⟨0, 4, 457⟩, ⟨2, 4, 510⟩], triples := #[⟨0, 1, 2⟩] }
def er184_233 : Row := { vars := #[280, 339, 340, 227], coeff := #[1, 1, 1, 1], bound := 2, weight := 229082, edges := #[⟨1, 3, 57⟩, ⟨2, 3, 171⟩], triples := #[⟨0, 1, 2⟩] }
def er184_234 : Row := { vars := #[282, 304, 368, 25], coeff := #[1, 1, 1, 1], bound := 2, weight := 446429, edges := #[⟨0, 3, 237⟩, ⟨1, 3, 325⟩], triples := #[⟨0, 1, 2⟩] }
def er184_235 : Row := { vars := #[287, 314, 350, 32], coeff := #[1, 1, 1, 1], bound := 2, weight := 306123, edges := #[⟨0, 3, 238⟩, ⟨2, 3, 261⟩], triples := #[⟨0, 1, 2⟩] }
def er184_236 : Row := { vars := #[292, 294, 366, 45], coeff := #[1, 1, 1, 1], bound := 2, weight := 493878, edges := #[⟨0, 3, 323⟩, ⟨1, 3, 247⟩], triples := #[⟨0, 1, 2⟩] }
def er184_237 : Row := { vars := #[292, 313, 345, 327], coeff := #[1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨0, 3, 510⟩, ⟨1, 3, 411⟩], triples := #[⟨0, 1, 2⟩] }
def er184_238 : Row := { vars := #[9], coeff := #[1], bound := 1, weight := 506123, edges := #[], triples := #[] }
def er184_239 : Row := { vars := #[10], coeff := #[1], bound := 1, weight := 36225, edges := #[], triples := #[] }
def er184_240 : Row := { vars := #[15], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er184_241 : Row := { vars := #[30], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er184_242 : Row := { vars := #[36], coeff := #[1], bound := 1, weight := 923980, edges := #[], triples := #[] }
def er184_243 : Row := { vars := #[47], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er184_244 : Row := { vars := #[48], coeff := #[1], bound := 1, weight := 487245, edges := #[], triples := #[] }
def er184_245 : Row := { vars := #[50], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er184_246 : Row := { vars := #[51], coeff := #[1], bound := 1, weight := 842858, edges := #[], triples := #[] }
def er184_247 : Row := { vars := #[56], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er184_248 : Row := { vars := #[59], coeff := #[1], bound := 1, weight := 877552, edges := #[], triples := #[] }
def er184_249 : Row := { vars := #[71], coeff := #[1], bound := 1, weight := 734184, edges := #[], triples := #[] }
def er184_250 : Row := { vars := #[75], coeff := #[1], bound := 1, weight := 403572, edges := #[], triples := #[] }
def er184_251 : Row := { vars := #[79], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er184_252 : Row := { vars := #[82], coeff := #[1], bound := 1, weight := 970919, edges := #[], triples := #[] }
def er184_253 : Row := { vars := #[84], coeff := #[1], bound := 1, weight := 850001, edges := #[], triples := #[] }
def er184_254 : Row := { vars := #[85], coeff := #[1], bound := 1, weight := 138776, edges := #[], triples := #[] }
def er184_255 : Row := { vars := #[87], coeff := #[1], bound := 1, weight := 472449, edges := #[], triples := #[] }
end HardyCapset20261020.Cert



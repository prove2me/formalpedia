-- Prove2me | Definitions.Def_HardyCapsetEvaluationData143rows03V420261021
-- name    : HardyCapsetEvaluationData143rows03V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:49:15.805309+00:00
-- url     : https://prove2.me/theorems/bcb2a4b3-6e9b-4414-a519-46ded1f47465
-- title:
--   HardyCapsetEvaluationData143rows03V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er143_192 : Row := { vars := #[146, 330, 370], coeff := #[1, 1, 1], bound := 1, weight := 955556, edges := #[⟨0, 1, 360⟩, ⟨0, 2, 332⟩, ⟨1, 2, 91⟩], triples := #[] }
def er143_193 : Row := { vars := #[148, 162, 170], coeff := #[1, 1, 1], bound := 1, weight := 355556, edges := #[⟨0, 1, 6⟩, ⟨0, 2, 31⟩, ⟨1, 2, 161⟩], triples := #[] }
def er143_194 : Row := { vars := #[150, 324, 330], coeff := #[1, 1, 1], bound := 1, weight := 44445, edges := #[⟨0, 1, 363⟩, ⟨0, 2, 359⟩, ⟨1, 2, 311⟩], triples := #[] }
def er143_195 : Row := { vars := #[152, 163, 302], coeff := #[1, 1, 1], bound := 1, weight := 133334, edges := #[⟨0, 1, 29⟩, ⟨0, 2, 449⟩, ⟨1, 2, 385⟩], triples := #[] }
def er143_196 : Row := { vars := #[152, 163, 366], coeff := #[1, 1, 1], bound := 1, weight := 866667, edges := #[⟨0, 1, 29⟩, ⟨0, 2, 303⟩, ⟨1, 2, 293⟩], triples := #[] }
def er143_197 : Row := { vars := #[154, 268, 409], coeff := #[1, 1, 1], bound := 1, weight := 688889, edges := #[⟨0, 1, 502⟩, ⟨0, 2, 287⟩, ⟨1, 2, 187⟩], triples := #[] }
def er143_198 : Row := { vars := #[154, 277, 370], coeff := #[1, 1, 1], bound := 1, weight := 44445, edges := #[⟨0, 1, 423⟩, ⟨0, 2, 350⟩, ⟨1, 2, 178⟩], triples := #[] }
def er143_199 : Row := { vars := #[157, 266, 431], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 494⟩, ⟨0, 2, 192⟩, ⟨1, 2, 99⟩], triples := #[] }
def er143_200 : Row := { vars := #[159, 421, 435], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 225⟩, ⟨0, 2, 214⟩, ⟨1, 2, 493⟩], triples := #[] }
def er143_201 : Row := { vars := #[160, 294, 414], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 407⟩, ⟨0, 2, 295⟩, ⟨1, 2, 79⟩], triples := #[] }
def er143_202 : Row := { vars := #[162, 170, 289], coeff := #[1, 1, 1], bound := 1, weight := 44445, edges := #[⟨0, 1, 161⟩, ⟨0, 2, 403⟩, ⟨1, 2, 400⟩], triples := #[] }
def er143_203 : Row := { vars := #[165, 175, 199], coeff := #[1, 1, 1], bound := 1, weight := 177778, edges := #[⟨0, 1, 166⟩, ⟨0, 2, 182⟩, ⟨1, 2, 191⟩], triples := #[] }
def er143_204 : Row := { vars := #[172, 200, 419], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 191⟩, ⟨0, 2, 305⟩, ⟨1, 2, 331⟩], triples := #[] }
def er143_205 : Row := { vars := #[173, 436, 280], coeff := #[1, 1, 1], bound := 1, weight := 311112, edges := #[⟨0, 1, 333⟩, ⟨0, 2, 367⟩, ⟨1, 2, 43⟩], triples := #[] }
def er143_206 : Row := { vars := #[174, 320, 424], coeff := #[1, 1, 1], bound := 1, weight := 177778, edges := #[⟨0, 1, 461⟩, ⟨0, 2, 301⟩, ⟨1, 2, 161⟩], triples := #[] }
def er143_207 : Row := { vars := #[183, 164, 326], coeff := #[1, 1, 1], bound := 1, weight := 177778, edges := #[⟨0, 1, 160⟩, ⟨0, 2, 495⟩, ⟨1, 2, 509⟩], triples := #[] }
def er143_208 : Row := { vars := #[189, 230, 231], coeff := #[1, 1, 1], bound := 1, weight := 711112, edges := #[⟨0, 1, 178⟩, ⟨0, 2, 177⟩, ⟨1, 2, 191⟩], triples := #[] }
def er143_209 : Row := { vars := #[209, 258, 418], coeff := #[1, 1, 1], bound := 1, weight := 911112, edges := #[⟨0, 1, 419⟩, ⟨0, 2, 345⟩, ⟨1, 2, 131⟩], triples := #[] }
def er143_210 : Row := { vars := #[209, 420, 325], coeff := #[1, 1, 1], bound := 1, weight := 88889, edges := #[⟨0, 1, 338⟩, ⟨0, 2, 475⟩, ⟨1, 2, 186⟩], triples := #[] }
def er143_211 : Row := { vars := #[213, 269, 311], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 405⟩, ⟨0, 2, 373⟩, ⟨1, 2, 333⟩], triples := #[] }
def er143_212 : Row := { vars := #[214, 396, 319], coeff := #[1, 1, 1], bound := 1, weight := 200000, edges := #[⟨0, 1, 225⟩, ⟨0, 2, 511⟩, ⟨1, 2, 37⟩], triples := #[] }
def er143_213 : Row := { vars := #[219, 389, 249], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 195⟩, ⟨0, 2, 418⟩, ⟨1, 2, 186⟩], triples := #[] }
def er143_214 : Row := { vars := #[234, 387, 212], coeff := #[1, 1, 1], bound := 1, weight := 333334, edges := #[⟨0, 1, 231⟩, ⟨0, 2, 167⟩, ⟨1, 2, 242⟩], triples := #[] }
def er143_215 : Row := { vars := #[234, 236, 295, 375], coeff := #[1, 1, 1, 1], bound := 1, weight := 355556, edges := #[⟨0, 1, 191⟩, ⟨0, 2, 383⟩, ⟨0, 3, 295⟩, ⟨1, 2, 379⟩, ⟨1, 3, 291⟩, ⟨2, 3, 159⟩], triples := #[] }
def er143_216 : Row := { vars := #[234, 236, 286, 375], coeff := #[1, 1, 1, 1], bound := 1, weight := 311112, edges := #[⟨0, 1, 191⟩, ⟨0, 2, 371⟩, ⟨0, 3, 295⟩, ⟨1, 2, 367⟩, ⟨1, 3, 291⟩, ⟨2, 3, 151⟩], triples := #[] }
def er143_217 : Row := { vars := #[236, 386, 212], coeff := #[1, 1, 1], bound := 1, weight := 333334, edges := #[⟨0, 1, 231⟩, ⟨0, 2, 164⟩, ⟨1, 2, 243⟩], triples := #[] }
def er143_218 : Row := { vars := #[273, 408, 382], coeff := #[1, 1, 1], bound := 1, weight := 155556, edges := #[⟨0, 1, 119⟩, ⟨0, 2, 99⟩, ⟨1, 2, 418⟩], triples := #[] }
def er143_219 : Row := { vars := #[277, 318, 404], coeff := #[1, 1, 1], bound := 1, weight := 777778, edges := #[⟨0, 1, 192⟩, ⟨0, 2, 118⟩, ⟨1, 2, 19⟩], triples := #[] }
def er143_220 : Row := { vars := #[281, 304, 377], coeff := #[1, 1, 1], bound := 1, weight := 288889, edges := #[⟨0, 1, 256⟩, ⟨0, 2, 91⟩, ⟨1, 2, 119⟩], triples := #[] }
def er143_221 : Row := { vars := #[288, 426, 406], coeff := #[1, 1, 1], bound := 1, weight := 311112, edges := #[⟨0, 1, 2⟩, ⟨0, 2, 73⟩, ⟨1, 2, 357⟩], triples := #[] }
def er143_222 : Row := { vars := #[290, 337, 335], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 207⟩, ⟨0, 2, 219⟩, ⟨1, 2, 347⟩], triples := #[] }
def er143_223 : Row := { vars := #[292, 336, 339], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 221⟩, ⟨0, 2, 209⟩, ⟨1, 2, 351⟩], triples := #[] }
def er143_224 : Row := { vars := #[298, 139, 407], coeff := #[1, 1, 1], bound := 1, weight := 600000, edges := #[⟨0, 1, 431⟩, ⟨0, 2, 73⟩, ⟨1, 2, 247⟩], triples := #[] }
def er143_225 : Row := { vars := #[300, 422, 381], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 19⟩, ⟨0, 2, 118⟩, ⟨1, 2, 352⟩], triples := #[] }
def er143_226 : Row := { vars := #[301, 391, 323], coeff := #[1, 1, 1], bound := 1, weight := 133334, edges := #[⟨0, 1, 83⟩, ⟨0, 2, 198⟩, ⟨1, 2, 9⟩], triples := #[] }
def er143_227 : Row := { vars := #[303, 322, 400], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 213⟩, ⟨0, 2, 81⟩, ⟨1, 2, 23⟩], triples := #[] }
def er143_228 : Row := { vars := #[360, 364, 376], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 391⟩, ⟨0, 2, 363⟩, ⟨1, 2, 359⟩], triples := #[] }
def er143_229 : Row := { vars := #[362, 374, 321], coeff := #[1, 1, 1], bound := 1, weight := 777778, edges := #[⟨0, 1, 352⟩, ⟨0, 2, 119⟩, ⟨1, 2, 91⟩], triples := #[] }
def er143_230 : Row := { vars := #[369, 402, 106], coeff := #[1, 1, 1], bound := 1, weight := 911112, edges := #[⟨0, 1, 489⟩, ⟨0, 2, 344⟩, ⟨1, 2, 291⟩], triples := #[] }
def er143_231 : Row := { vars := #[371, 415, 373], coeff := #[1, 1, 1], bound := 1, weight := 577778, edges := #[⟨0, 1, 494⟩, ⟨0, 2, 401⟩, ⟨1, 2, 493⟩], triples := #[] }
def er143_232 : Row := { vars := #[372, 415, 374], coeff := #[1, 1, 1], bound := 1, weight := 222223, edges := #[⟨0, 1, 492⟩, ⟨0, 2, 397⟩, ⟨1, 2, 503⟩], triples := #[] }
def er143_233 : Row := { vars := #[378, 423, 382], coeff := #[1, 1, 1], bound := 1, weight := 377778, edges := #[⟨0, 1, 363⟩, ⟨0, 2, 411⟩, ⟨1, 2, 359⟩], triples := #[] }
def er143_234 : Row := { vars := #[379, 385, 423], coeff := #[1, 1, 1], bound := 1, weight := 622223, edges := #[⟨0, 1, 407⟩, ⟨0, 2, 355⟩, ⟨1, 2, 375⟩], triples := #[] }
def er143_235 : Row := { vars := #[439, 441, 321], coeff := #[1, 1, 1], bound := 1, weight := 222223, edges := #[⟨0, 1, 507⟩, ⟨0, 2, 146⟩, ⟨1, 2, 166⟩], triples := #[] }
def er143_236 : Row := { vars := #[439, 441, 255], coeff := #[1, 1, 1], bound := 1, weight := 377778, edges := #[⟨0, 1, 507⟩, ⟨0, 2, 87⟩, ⟨1, 2, 107⟩], triples := #[] }
def er143_237 : Row := { vars := #[440, 443, 164], coeff := #[1, 1, 1], bound := 1, weight := 822223, edges := #[⟨0, 1, 511⟩, ⟨0, 2, 311⟩, ⟨1, 2, 321⟩], triples := #[] }
def er143_238 : Row := { vars := #[440, 443, 444], coeff := #[1, 1, 1], bound := 1, weight := 177778, edges := #[⟨0, 1, 511⟩, ⟨0, 2, 508⟩, ⟨1, 2, 502⟩], triples := #[] }
def er143_239 : Row := { vars := #[35, 87, 226, 4, 233], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 177778, edges := #[⟨3, 4, 96⟩, ⟨1, 3, 180⟩, ⟨2, 3, 99⟩, ⟨1, 4, 19⟩, ⟨2, 4, 183⟩], triples := #[⟨0, 1, 2⟩] }
def er143_240 : Row := { vars := #[224, 225, 226, 216, 222], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 190⟩, ⟨0, 3, 188⟩, ⟨2, 3, 189⟩, ⟨0, 4, 186⟩, ⟨2, 4, 187⟩], triples := #[⟨0, 1, 2⟩] }
def er143_241 : Row := { vars := #[226, 239, 399, 198, 414], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 200⟩, ⟨0, 3, 159⟩, ⟨1, 3, 436⟩, ⟨0, 4, 235⟩, ⟨1, 4, 175⟩], triples := #[⟨0, 1, 2⟩] }
def er143_242 : Row := { vars := #[226, 248, 390, 204, 414], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 192⟩, ⟨0, 3, 151⟩, ⟨1, 3, 436⟩, ⟨0, 4, 235⟩, ⟨1, 4, 177⟩], triples := #[⟨0, 1, 2⟩] }
def er143_243 : Row := { vars := #[226, 286, 352, 112, 116, 310], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 44445, edges := #[⟨3, 4, 101⟩, ⟨3, 5, 434⟩, ⟨4, 5, 430⟩, ⟨0, 3, 9⟩, ⟨2, 3, 307⟩, ⟨0, 4, 1⟩, ⟨2, 4, 306⟩, ⟨0, 5, 395⟩, ⟨2, 5, 177⟩], triples := #[⟨0, 1, 2⟩] }
def er143_244 : Row := { vars := #[226, 338, 444, 320, 424, 233, 235], coeff := #[1, 1, 1, 1, 1, 1, 1], bound := 2, weight := 822223, edges := #[⟨3, 4, 161⟩, ⟨3, 5, 487⟩, ⟨3, 6, 483⟩, ⟨4, 5, 327⟩, ⟨4, 6, 323⟩, ⟨5, 6, 190⟩, ⟨0, 3, 469⟩, ⟨2, 3, 169⟩, ⟨0, 4, 309⟩, ⟨1, 4, 171⟩, ⟨0, 5, 183⟩, ⟨2, 5, 331⟩, ⟨0, 6, 181⟩, ⟨1, 6, 491⟩], triples := #[⟨0, 1, 2⟩] }
def er143_245 : Row := { vars := #[226, 340, 442, 332, 42, 436, 38], coeff := #[1, 1, 1, 1, 1, 1, 1], bound := 2, weight := 688889, edges := #[⟨3, 4, 431⟩, ⟨3, 5, 179⟩, ⟨3, 6, 435⟩, ⟨4, 5, 271⟩, ⟨4, 6, 29⟩, ⟨5, 6, 275⟩, ⟨0, 3, 459⟩, ⟨2, 3, 141⟩, ⟨0, 4, 73⟩, ⟨2, 4, 245⟩, ⟨0, 5, 299⟩, ⟨1, 5, 133⟩, ⟨0, 6, 81⟩, ⟨1, 6, 405⟩], triples := #[⟨0, 1, 2⟩] }
def er143_246 : Row := { vars := #[13], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er143_247 : Row := { vars := #[15], coeff := #[1], bound := 1, weight := 800000, edges := #[], triples := #[] }
def er143_248 : Row := { vars := #[35], coeff := #[1], bound := 1, weight := 822223, edges := #[], triples := #[] }
def er143_249 : Row := { vars := #[39], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er143_250 : Row := { vars := #[52], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er143_251 : Row := { vars := #[83], coeff := #[1], bound := 1, weight := 600001, edges := #[], triples := #[] }
def er143_252 : Row := { vars := #[87], coeff := #[1], bound := 1, weight := 822223, edges := #[], triples := #[] }
def er143_253 : Row := { vars := #[109], coeff := #[1], bound := 1, weight := 622223, edges := #[], triples := #[] }
def er143_254 : Row := { vars := #[113], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er143_255 : Row := { vars := #[151], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
end HardyCapset20261020.Cert



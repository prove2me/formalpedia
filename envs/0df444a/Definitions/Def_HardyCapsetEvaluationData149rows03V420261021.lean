-- Prove2me | Definitions.Def_HardyCapsetEvaluationData149rows03V420261021
-- name    : HardyCapsetEvaluationData149rows03V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:58:26.302095+00:00
-- url     : https://prove2.me/theorems/e18a21e6-04c9-4cdc-8d58-b4a4d8fb3254
-- title:
--   HardyCapsetEvaluationData149rows03V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er149_192 : Row := { vars := #[87, 368, 283], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 242⟩, ⟨0, 2, 465⟩, ⟨1, 2, 166⟩], triples := #[] }
def er149_193 : Row := { vars := #[90, 26, 356], coeff := #[1, 1, 1], bound := 1, weight := 892858, edges := #[⟨0, 1, 189⟩, ⟨0, 2, 331⟩, ⟨1, 2, 231⟩], triples := #[] }
def er149_194 : Row := { vars := #[91, 226, 99], coeff := #[1, 1, 1], bound := 1, weight := 607143, edges := #[⟨0, 1, 27⟩, ⟨0, 2, 73⟩, ⟨1, 2, 31⟩], triples := #[] }
def er149_195 : Row := { vars := #[91, 102, 104], coeff := #[1, 1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 99⟩, ⟨0, 2, 98⟩, ⟨1, 2, 89⟩], triples := #[] }
def er149_196 : Row := { vars := #[92, 101, 415], coeff := #[1, 1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 99⟩, ⟨0, 2, 236⟩, ⟨1, 2, 241⟩], triples := #[] }
def er149_197 : Row := { vars := #[96, 227, 278], coeff := #[1, 1, 1], bound := 1, weight := 571429, edges := #[⟨0, 1, 35⟩, ⟨0, 2, 436⟩, ⟨1, 2, 377⟩], triples := #[] }
def er149_198 : Row := { vars := #[96, 278, 222], coeff := #[1, 1, 1], bound := 1, weight := 250000, edges := #[⟨0, 1, 436⟩, ⟨0, 2, 3⟩, ⟨1, 2, 356⟩], triples := #[] }
def er149_199 : Row := { vars := #[102, 397, 219, 308], coeff := #[1, 1, 1, 1], bound := 1, weight := 678572, edges := #[⟨0, 1, 264⟩, ⟨0, 2, 39⟩, ⟨0, 3, 355⟩, ⟨1, 2, 193⟩, ⟨1, 3, 11⟩, ⟨2, 3, 504⟩], triples := #[] }
def er149_200 : Row := { vars := #[107, 125, 218], coeff := #[1, 1, 1], bound := 1, weight := 500001, edges := #[⟨0, 1, 74⟩, ⟨0, 2, 42⟩, ⟨1, 2, 67⟩], triples := #[] }
def er149_201 : Row := { vars := #[108, 232, 284], coeff := #[1, 1, 1], bound := 1, weight := 250000, edges := #[⟨0, 1, 12⟩, ⟨0, 2, 436⟩, ⟨1, 2, 377⟩], triples := #[] }
def er149_202 : Row := { vars := #[109, 150, 218], coeff := #[1, 1, 1], bound := 1, weight := 142858, edges := #[⟨0, 1, 122⟩, ⟨0, 2, 39⟩, ⟨1, 2, 34⟩], triples := #[] }
def er149_203 : Row := { vars := #[111, 375, 156, 271], coeff := #[1, 1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 250⟩, ⟨0, 2, 116⟩, ⟨0, 3, 410⟩, ⟨1, 2, 268⟩, ⟨1, 3, 90⟩, ⟨2, 3, 428⟩], triples := #[] }
def er149_204 : Row := { vars := #[112, 119, 79], coeff := #[1, 1, 1], bound := 1, weight := 678572, edges := #[⟨0, 1, 74⟩, ⟨0, 2, 169⟩, ⟨1, 2, 177⟩], triples := #[] }
def er149_205 : Row := { vars := #[114, 133, 116], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 130⟩, ⟨0, 2, 96⟩, ⟨1, 2, 129⟩], triples := #[] }
def er149_206 : Row := { vars := #[115, 207, 117], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 65⟩, ⟨0, 2, 78⟩, ⟨1, 2, 60⟩], triples := #[] }
def er149_207 : Row := { vars := #[119, 403, 219, 308], coeff := #[1, 1, 1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 274⟩, ⟨0, 2, 67⟩, ⟨0, 3, 375⟩, ⟨1, 2, 213⟩, ⟨1, 3, 34⟩, ⟨2, 3, 504⟩], triples := #[] }
def er149_208 : Row := { vars := #[120, 148, 408], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 128⟩, ⟨0, 2, 194⟩, ⟨1, 2, 235⟩], triples := #[] }
def er149_209 : Row := { vars := #[122, 215, 292, 408], coeff := #[1, 1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 63⟩, ⟨0, 2, 417⟩, ⟨0, 3, 193⟩, ⟨1, 2, 355⟩, ⟨1, 3, 330⟩, ⟨2, 3, 17⟩], triples := #[] }
def er149_210 : Row := { vars := #[122, 215, 292, 364], coeff := #[1, 1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 63⟩, ⟨0, 2, 417⟩, ⟨0, 3, 310⟩, ⟨1, 2, 355⟩, ⟨1, 3, 245⟩, ⟨2, 3, 185⟩], triples := #[] }
def er149_211 : Row := { vars := #[129, 219, 140], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 70⟩, ⟨0, 2, 120⟩, ⟨1, 2, 3⟩], triples := #[] }
def er149_212 : Row := { vars := #[132, 103, 142], coeff := #[1, 1, 1], bound := 1, weight := 892858, edges := #[⟨0, 1, 128⟩, ⟨0, 2, 117⟩, ⟨1, 2, 124⟩], triples := #[] }
def er149_213 : Row := { vars := #[134, 162, 203], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 98⟩, ⟨0, 2, 53⟩, ⟨1, 2, 13⟩], triples := #[] }
def er149_214 : Row := { vars := #[136, 154, 157], coeff := #[1, 1, 1], bound := 1, weight := 285715, edges := #[⟨0, 1, 74⟩, ⟨0, 2, 102⟩, ⟨1, 2, 128⟩], triples := #[] }
def er149_215 : Row := { vars := #[138, 176, 277], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 46⟩, ⟨0, 2, 417⟩, ⟨1, 2, 395⟩], triples := #[] }
def er149_216 : Row := { vars := #[141, 205, 61], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 27⟩, ⟨0, 2, 163⟩, ⟨1, 2, 73⟩], triples := #[] }
def er149_217 : Row := { vars := #[143, 61, 395], coeff := #[1, 1, 1], bound := 1, weight := 178572, edges := #[⟨0, 1, 161⟩, ⟨0, 2, 250⟩, ⟨1, 2, 347⟩], triples := #[] }
def er149_218 : Row := { vars := #[144, 300, 396], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 405⟩, ⟨0, 2, 250⟩, ⟨1, 2, 120⟩], triples := #[] }
def er149_219 : Row := { vars := #[145, 213, 238], coeff := #[1, 1, 1], bound := 1, weight := 714286, edges := #[⟨0, 1, 18⟩, ⟨0, 2, 507⟩, ⟨1, 2, 455⟩], triples := #[] }
def er149_220 : Row := { vars := #[146, 161, 239], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 90⟩, ⟨0, 2, 507⟩, ⟨1, 2, 487⟩], triples := #[] }
def er149_221 : Row := { vars := #[146, 172, 168, 158], coeff := #[1, 1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 65⟩, ⟨0, 2, 67⟩, ⟨0, 3, 93⟩, ⟨1, 2, 141⟩, ⟨1, 3, 34⟩, ⟨2, 3, 27⟩], triples := #[] }
def er149_222 : Row := { vars := #[147, 198, 150], coeff := #[1, 1, 1], bound := 1, weight := 250001, edges := #[⟨0, 1, 63⟩, ⟨0, 2, 116⟩, ⟨1, 2, 65⟩], triples := #[] }
def er149_223 : Row := { vars := #[152, 202, 191], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 66⟩, ⟨0, 2, 37⟩, ⟨1, 2, 144⟩], triples := #[] }
def er149_224 : Row := { vars := #[153, 139, 175], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 99⟩, ⟨0, 2, 1⟩, ⟨1, 2, 66⟩], triples := #[] }
def er149_225 : Row := { vars := #[156, 177, 221], coeff := #[1, 1, 1], bound := 1, weight := 178572, edges := #[⟨0, 1, 32⟩, ⟨0, 2, 40⟩, ⟨1, 2, 177⟩], triples := #[] }
def er149_226 : Row := { vars := #[158, 168, 392], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 27⟩, ⟨0, 2, 289⟩, ⟨1, 2, 225⟩], triples := #[] }
def er149_227 : Row := { vars := #[164, 235, 299], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 67⟩, ⟨0, 2, 455⟩, ⟨1, 2, 401⟩], triples := #[] }
def er149_228 : Row := { vars := #[165, 261, 296], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 491⟩, ⟨0, 2, 449⟩, ⟨1, 2, 332⟩], triples := #[] }
def er149_229 : Row := { vars := #[169, 176, 192], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 139⟩, ⟨0, 2, 164⟩, ⟨1, 2, 166⟩], triples := #[] }
def er149_230 : Row := { vars := #[169, 313, 315], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 493⟩, ⟨0, 2, 503⟩, ⟨1, 2, 321⟩], triples := #[] }
def er149_231 : Row := { vars := #[172, 205, 179], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 182⟩, ⟨0, 2, 165⟩, ⟨1, 2, 188⟩], triples := #[] }
def er149_232 : Row := { vars := #[177, 221, 229], coeff := #[1, 1, 1], bound := 1, weight := 178572, edges := #[⟨0, 1, 177⟩, ⟨0, 2, 173⟩, ⟨1, 2, 191⟩], triples := #[] }
def er149_233 : Row := { vars := #[179, 424, 202, 331], coeff := #[1, 1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 332⟩, ⟨0, 2, 136⟩, ⟨0, 3, 477⟩, ⟨1, 2, 344⟩, ⟨1, 3, 143⟩, ⟨2, 3, 470⟩], triples := #[] }
def er149_234 : Row := { vars := #[182, 173, 382], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 165⟩, ⟨0, 2, 242⟩, ⟨1, 2, 235⟩], triples := #[] }
def er149_235 : Row := { vars := #[188, 193, 272, 417], coeff := #[1, 1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 150⟩, ⟨0, 2, 368⟩, ⟨0, 3, 351⟩, ⟨1, 2, 364⟩, ⟨1, 3, 347⟩, ⟨2, 3, 65⟩], triples := #[] }
def er149_236 : Row := { vars := #[194, 231, 304], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 177⟩, ⟨0, 2, 459⟩, ⟨1, 2, 470⟩], triples := #[] }
def er149_237 : Row := { vars := #[195, 320, 199, 444], coeff := #[1, 1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 503⟩, ⟨0, 2, 167⟩, ⟨0, 3, 323⟩, ⟨1, 2, 508⟩, ⟨1, 3, 163⟩, ⟨2, 3, 321⟩], triples := #[] }
def er149_238 : Row := { vars := #[195, 424, 199, 340], coeff := #[1, 1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 343⟩, ⟨0, 2, 167⟩, ⟨0, 3, 483⟩, ⟨1, 2, 348⟩, ⟨1, 3, 163⟩, ⟨2, 3, 481⟩], triples := #[] }
def er149_239 : Row := { vars := #[198, 388, 430], coeff := #[1, 1, 1], bound := 1, weight := 750000, edges := #[⟨0, 1, 242⟩, ⟨0, 2, 347⟩, ⟨1, 2, 393⟩], triples := #[] }
def er149_240 : Row := { vars := #[206, 209, 97], coeff := #[1, 1, 1], bound := 1, weight := 500001, edges := #[⟨0, 1, 177⟩, ⟨0, 2, 38⟩, ⟨1, 2, 66⟩], triples := #[] }
def er149_241 : Row := { vars := #[206, 209, 275], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 177⟩, ⟨0, 2, 386⟩, ⟨1, 2, 391⟩], triples := #[] }
def er149_242 : Row := { vars := #[217, 320, 305], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 481⟩, ⟨0, 2, 490⟩, ⟨1, 2, 332⟩], triples := #[] }
def er149_243 : Row := { vars := #[217, 365, 400], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 245⟩, ⟨0, 2, 213⟩, ⟨1, 2, 492⟩], triples := #[] }
def er149_244 : Row := { vars := #[218, 399, 285], coeff := #[1, 1, 1], bound := 1, weight := 357143, edges := #[⟨0, 1, 221⟩, ⟨0, 2, 391⟩, ⟨1, 2, 104⟩], triples := #[] }
def er149_245 : Row := { vars := #[219, 387, 295], coeff := #[1, 1, 1], bound := 1, weight := 321429, edges := #[⟨0, 1, 231⟩, ⟨0, 2, 377⟩, ⟨1, 2, 107⟩], triples := #[] }
def er149_246 : Row := { vars := #[220, 224, 228], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 188⟩, ⟨0, 2, 190⟩, ⟨1, 2, 184⟩], triples := #[] }
def er149_247 : Row := { vars := #[221, 225, 286], coeff := #[1, 1, 1], bound := 1, weight := 357143, edges := #[⟨0, 1, 189⟩, ⟨0, 2, 396⟩, ⟨1, 2, 401⟩], triples := #[] }
def er149_248 : Row := { vars := #[235, 262, 399], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 436⟩, ⟨0, 2, 242⟩, ⟨1, 2, 182⟩], triples := #[] }
def er149_249 : Row := { vars := #[236, 387, 296], coeff := #[1, 1, 1], bound := 1, weight := 357143, edges := #[⟨0, 1, 213⟩, ⟨0, 2, 402⟩, ⟨1, 2, 105⟩], triples := #[] }
def er149_250 : Row := { vars := #[238, 312, 381], coeff := #[1, 1, 1], bound := 1, weight := 35715, edges := #[⟨0, 1, 278⟩, ⟨0, 2, 183⟩, ⟨1, 2, 13⟩], triples := #[] }
def er149_251 : Row := { vars := #[244, 327, 329], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 270⟩, ⟨0, 2, 260⟩, ⟨1, 2, 344⟩], triples := #[] }
def er149_252 : Row := { vars := #[246, 328, 333], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 274⟩, ⟨0, 2, 264⟩, ⟨1, 2, 348⟩], triples := #[] }
def er149_253 : Row := { vars := #[251, 421, 361], coeff := #[1, 1, 1], bound := 1, weight := 178572, edges := #[⟨0, 1, 116⟩, ⟨0, 2, 17⟩, ⟨1, 2, 417⟩], triples := #[] }
def er149_254 : Row := { vars := #[251, 395, 374], coeff := #[1, 1, 1], bound := 1, weight := 821429, edges := #[⟨0, 1, 158⟩, ⟨0, 2, 191⟩, ⟨1, 2, 418⟩], triples := #[] }
def er149_255 : Row := { vars := #[253, 257, 265], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 226⟩, ⟨0, 2, 199⟩, ⟨1, 2, 215⟩], triples := #[] }
end HardyCapset20261020.Cert



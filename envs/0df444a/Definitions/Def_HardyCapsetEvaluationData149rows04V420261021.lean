-- Prove2me | Definitions.Def_HardyCapsetEvaluationData149rows04V420261021
-- name    : HardyCapsetEvaluationData149rows04V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:58:36.030662+00:00
-- url     : https://prove2.me/theorems/24782153-2047-42fd-8435-67ded9749a89
-- title:
--   HardyCapsetEvaluationData149rows04V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er149_256 : Row := { vars := #[255, 261, 390], coeff := #[1, 1, 1], bound := 1, weight := 500001, edges := #[⟨0, 1, 200⟩, ⟨0, 2, 158⟩, ⟨1, 2, 191⟩], triples := #[] }
def er149_257 : Row := { vars := #[260, 266, 296], coeff := #[1, 1, 1], bound := 1, weight := 142858, edges := #[⟨0, 1, 236⟩, ⟨0, 2, 333⟩, ⟨1, 2, 343⟩], triples := #[] }
def er149_258 : Row := { vars := #[267, 421, 361], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 62⟩, ⟨0, 2, 184⟩, ⟨1, 2, 417⟩], triples := #[] }
def er149_259 : Row := { vars := #[270, 291, 355], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 258⟩, ⟨0, 2, 191⟩, ⟨1, 2, 158⟩], triples := #[] }
def er149_260 : Row := { vars := #[277, 416, 342], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 13⟩, ⟨0, 2, 183⟩, ⟨1, 2, 438⟩], triples := #[] }
def er149_261 : Row := { vars := #[284, 391, 345], coeff := #[1, 1, 1], bound := 1, weight := 750001, edges := #[⟨0, 1, 93⟩, ⟨0, 2, 180⟩, ⟨1, 2, 481⟩], triples := #[] }
def er149_262 : Row := { vars := #[286, 431, 433], coeff := #[1, 1, 1], bound := 1, weight := 642858, edges := #[⟨0, 1, 46⟩, ⟨0, 2, 69⟩, ⟨1, 2, 504⟩], triples := #[] }
def er149_263 : Row := { vars := #[289, 312, 386], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 213⟩, ⟨0, 2, 81⟩, ⟨1, 2, 23⟩], triples := #[] }
def er149_264 : Row := { vars := #[311, 414, 376], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 184⟩, ⟨0, 2, 62⟩, ⟨1, 2, 356⟩], triples := #[] }
def er149_265 : Row := { vars := #[321, 180, 438], coeff := #[1, 1, 1], bound := 1, weight := 357143, edges := #[⟨0, 1, 492⟩, ⟨0, 2, 134⟩, ⟨1, 2, 313⟩], triples := #[] }
def er149_266 : Row := { vars := #[350, 432, 437], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 434⟩, ⟨0, 2, 424⟩, ⟨1, 2, 508⟩], triples := #[] }
def er149_267 : Row := { vars := #[373, 377, 412], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 406⟩, ⟨0, 2, 359⟩, ⟨1, 2, 375⟩], triples := #[] }
def er149_268 : Row := { vars := #[377, 27, 412], coeff := #[1, 1, 1], bound := 1, weight := 714286, edges := #[⟨0, 1, 331⟩, ⟨0, 2, 375⟩, ⟨1, 2, 278⟩], triples := #[] }
def er149_269 : Row := { vars := #[20, 123, 230, 23, 235], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000001, edges := #[⟨3, 4, 78⟩, ⟨1, 3, 182⟩, ⟨2, 3, 89⟩, ⟨1, 4, 29⟩, ⟨2, 4, 181⟩], triples := #[⟨0, 1, 2⟩] }
def er149_270 : Row := { vars := #[68, 160, 230, 154, 157], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 714286, edges := #[⟨3, 4, 128⟩, ⟨1, 3, 130⟩, ⟨2, 3, 65⟩, ⟨1, 4, 124⟩, ⟨2, 4, 53⟩], triples := #[⟨0, 1, 2⟩] }
def er149_271 : Row := { vars := #[183, 212, 230, 170, 178], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 159⟩, ⟨0, 3, 161⟩, ⟨2, 3, 179⟩, ⟨0, 4, 149⟩, ⟨2, 4, 173⟩], triples := #[⟨0, 1, 2⟩] }
def er149_272 : Row := { vars := #[230, 237, 385, 264, 50, 46], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 377⟩, ⟨3, 5, 381⟩, ⟨4, 5, 27⟩, ⟨0, 3, 436⟩, ⟨2, 3, 161⟩, ⟨0, 4, 73⟩, ⟨2, 4, 323⟩, ⟨0, 5, 81⟩, ⟨2, 5, 327⟩], triples := #[⟨0, 1, 2⟩] }
def er149_273 : Row := { vars := #[230, 332, 440, 128, 124, 309, 413], coeff := #[1, 1, 1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 99⟩, ⟨3, 5, 379⟩, ⟨3, 6, 219⟩, ⟨4, 5, 383⟩, ⟨4, 6, 223⟩, ⟨5, 6, 159⟩, ⟨0, 3, 1⟩, ⟨1, 3, 385⟩, ⟨0, 4, 9⟩, ⟨2, 4, 225⟩, ⟨0, 5, 469⟩, ⟨2, 5, 169⟩, ⟨0, 6, 309⟩, ⟨1, 6, 171⟩], triples := #[⟨0, 1, 2⟩] }
def er149_274 : Row := { vars := #[230, 336, 436, 321, 425, 234, 236], coeff := #[1, 1, 1, 1, 1, 1, 1], bound := 2, weight := 642858, edges := #[⟨3, 4, 177⟩, ⟨3, 5, 467⟩, ⟨3, 6, 466⟩, ⟨4, 5, 307⟩, ⟨4, 6, 306⟩, ⟨5, 6, 189⟩, ⟨0, 3, 459⟩, ⟨2, 3, 141⟩, ⟨0, 4, 299⟩, ⟨1, 4, 133⟩, ⟨0, 5, 182⟩, ⟨1, 5, 490⟩, ⟨0, 6, 180⟩, ⟨2, 6, 330⟩], triples := #[⟨0, 1, 2⟩] }
def er149_275 : Row := { vars := #[49], coeff := #[1], bound := 1, weight := 642858, edges := #[], triples := #[] }
def er149_276 : Row := { vars := #[94], coeff := #[1], bound := 1, weight := 857143, edges := #[], triples := #[] }
def er149_277 : Row := { vars := #[106], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_278 : Row := { vars := #[127], coeff := #[1], bound := 1, weight := 714286, edges := #[], triples := #[] }
def er149_279 : Row := { vars := #[175], coeff := #[1], bound := 1, weight := 178572, edges := #[], triples := #[] }
def er149_280 : Row := { vars := #[184], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er149_281 : Row := { vars := #[189], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_282 : Row := { vars := #[229], coeff := #[1], bound := 1, weight := 821429, edges := #[], triples := #[] }
def er149_283 : Row := { vars := #[245], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_284 : Row := { vars := #[247], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_285 : Row := { vars := #[248], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_286 : Row := { vars := #[263], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_287 : Row := { vars := #[276], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_288 : Row := { vars := #[281], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_289 : Row := { vars := #[298], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_290 : Row := { vars := #[300], coeff := #[1], bound := 1, weight := 500000, edges := #[], triples := #[] }
def er149_291 : Row := { vars := #[303], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_292 : Row := { vars := #[306], coeff := #[1], bound := 1, weight := 785715, edges := #[], triples := #[] }
def er149_293 : Row := { vars := #[307], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_294 : Row := { vars := #[314], coeff := #[1], bound := 1, weight := 178572, edges := #[], triples := #[] }
def er149_295 : Row := { vars := #[319], coeff := #[1], bound := 1, weight := 964286, edges := #[], triples := #[] }
def er149_296 : Row := { vars := #[323], coeff := #[1], bound := 1, weight := 1000001, edges := #[], triples := #[] }
def er149_297 : Row := { vars := #[325], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_298 : Row := { vars := #[331], coeff := #[1], bound := 1, weight := 178572, edges := #[], triples := #[] }
def er149_299 : Row := { vars := #[335], coeff := #[1], bound := 1, weight := 357143, edges := #[], triples := #[] }
def er149_300 : Row := { vars := #[337], coeff := #[1], bound := 1, weight := 142858, edges := #[], triples := #[] }
def er149_301 : Row := { vars := #[338], coeff := #[1], bound := 1, weight := 571429, edges := #[], triples := #[] }
def er149_302 : Row := { vars := #[339], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er149_303 : Row := { vars := #[341], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_304 : Row := { vars := #[342], coeff := #[1], bound := 1, weight := 500000, edges := #[], triples := #[] }
def er149_305 : Row := { vars := #[343], coeff := #[1], bound := 1, weight := 321429, edges := #[], triples := #[] }
def er149_306 : Row := { vars := #[344], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_307 : Row := { vars := #[348], coeff := #[1], bound := 1, weight := 642858, edges := #[], triples := #[] }
def er149_308 : Row := { vars := #[349], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_309 : Row := { vars := #[351], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_310 : Row := { vars := #[352], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_311 : Row := { vars := #[356], coeff := #[1], bound := 1, weight := 107143, edges := #[], triples := #[] }
def er149_312 : Row := { vars := #[357], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_313 : Row := { vars := #[363], coeff := #[1], bound := 1, weight := 964286, edges := #[], triples := #[] }
def er149_314 : Row := { vars := #[366], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_315 : Row := { vars := #[367], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_316 : Row := { vars := #[372], coeff := #[1], bound := 1, weight := 321429, edges := #[], triples := #[] }
def er149_317 : Row := { vars := #[380], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_318 : Row := { vars := #[383], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er149_319 : Row := { vars := #[384], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
end HardyCapset20261020.Cert



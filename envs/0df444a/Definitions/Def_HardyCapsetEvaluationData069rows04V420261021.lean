-- Prove2me | Definitions.Def_HardyCapsetEvaluationData069rows04V420261021
-- name    : HardyCapsetEvaluationData069rows04V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T02:43:43.297944+00:00
-- url     : https://prove2.me/theorems/17b5fd12-bbb8-409b-8178-84122b12f462
-- title:
--   HardyCapsetEvaluationData069rows04V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er069_256 : Row := { vars := #[197, 198, 243], coeff := #[1, 1, 1], bound := 1, weight := 274391, edges := #[⟨0, 1, 253⟩, ⟨0, 2, 211⟩, ⟨1, 2, 207⟩], triples := #[] }
def er069_257 : Row := { vars := #[200, 410, 220], coeff := #[1, 1, 1], bound := 1, weight := 993903, edges := #[⟨0, 1, 1⟩, ⟨0, 2, 264⟩, ⟨1, 2, 16⟩], triples := #[] }
def er069_258 : Row := { vars := #[201, 211, 380], coeff := #[1, 1, 1], bound := 1, weight := 500001, edges := #[⟨0, 1, 273⟩, ⟨0, 2, 72⟩, ⟨1, 2, 100⟩], triples := #[] }
def er069_259 : Row := { vars := #[206, 406, 417], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 1⟩, ⟨0, 2, 27⟩, ⟨1, 2, 486⟩], triples := #[] }
def er069_260 : Row := { vars := #[224, 320, 242], coeff := #[1, 1, 1], bound := 1, weight := 335366, edges := #[⟨0, 1, 132⟩, ⟨0, 2, 225⟩, ⟨1, 2, 121⟩], triples := #[] }
def er069_261 : Row := { vars := #[224, 265, 332], coeff := #[1, 1, 1], bound := 1, weight := 1, edges := #[⟨0, 1, 220⟩, ⟨0, 2, 180⟩, ⟨1, 2, 98⟩], triples := #[] }
def er069_262 : Row := { vars := #[225, 239, 397], coeff := #[1, 1, 1], bound := 1, weight := 500000, edges := #[⟨0, 1, 286⟩, ⟨0, 2, 1⟩, ⟨1, 2, 17⟩], triples := #[] }
def er069_263 : Row := { vars := #[226, 329, 256], coeff := #[1, 1, 1], bound := 1, weight := 390244, edges := #[⟨0, 1, 183⟩, ⟨0, 2, 192⟩, ⟨1, 2, 82⟩], triples := #[] }
def er069_264 : Row := { vars := #[228, 390, 314], coeff := #[1, 1, 1], bound := 1, weight := 274391, edges := #[⟨0, 1, 126⟩, ⟨0, 2, 132⟩, ⟨1, 2, 464⟩], triples := #[] }
def er069_265 : Row := { vars := #[243, 354, 297], coeff := #[1, 1, 1], bound := 1, weight := 225610, edges := #[⟨0, 1, 44⟩, ⟨0, 2, 82⟩, ⟨1, 2, 492⟩], triples := #[] }
def er069_266 : Row := { vars := #[245, 378, 423], coeff := #[1, 1, 1], bound := 1, weight := 164635, edges := #[⟨0, 1, 0⟩, ⟨0, 2, 186⟩, ⟨1, 2, 369⟩], triples := #[] }
def er069_267 : Row := { vars := #[254, 273, 332], coeff := #[1, 1, 1], bound := 1, weight := 890244, edges := #[⟨0, 1, 318⟩, ⟨0, 2, 72⟩, ⟨1, 2, 88⟩], triples := #[] }
def er069_268 : Row := { vars := #[258, 416, 314], coeff := #[1, 1, 1], bound := 1, weight := 170732, edges := #[⟨0, 1, 179⟩, ⟨0, 2, 109⟩, ⟨1, 2, 434⟩], triples := #[] }
def er069_269 : Row := { vars := #[258, 429, 356], coeff := #[1, 1, 1], bound := 1, weight := 829269, edges := #[⟨0, 1, 132⟩, ⟨0, 2, 3⟩, ⟨1, 2, 353⟩], triples := #[] }
def er069_270 : Row := { vars := #[278, 286, 332], coeff := #[1, 1, 1], bound := 1, weight := 103659, edges := #[⟨0, 1, 348⟩, ⟨0, 2, 120⟩, ⟨1, 2, 128⟩], triples := #[] }
def er069_271 : Row := { vars := #[280, 430, 437], coeff := #[1, 1, 1], bound := 1, weight := 603659, edges := #[⟨0, 1, 180⟩, ⟨0, 2, 190⟩, ⟨1, 2, 511⟩], triples := #[] }
def er069_272 : Row := { vars := #[302, 27, 319], coeff := #[1, 1, 1], bound := 1, weight := 725610, edges := #[⟨0, 1, 225⟩, ⟨0, 2, 402⟩, ⟨1, 2, 207⟩], triples := #[] }
def er069_273 : Row := { vars := #[329, 433, 436], coeff := #[1, 1, 1], bound := 1, weight := 609757, edges := #[⟨0, 1, 455⟩, ⟨0, 2, 451⟩, ⟨1, 2, 500⟩], triples := #[] }
def er069_274 : Row := { vars := #[343, 370, 373], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 445⟩, ⟨0, 2, 441⟩, ⟨1, 2, 434⟩], triples := #[] }
def er069_275 : Row := { vars := #[347, 395, 348], coeff := #[1, 1, 1], bound := 1, weight := 1000000, edges := #[⟨0, 1, 383⟩, ⟨0, 2, 410⟩, ⟨1, 2, 379⟩], triples := #[] }
def er069_276 : Row := { vars := #[0, 8, 12, 132, 137, 11, 7], coeff := #[1, 1, 1, 1, 1, 1, 1], bound := 2, weight := 109757, edges := #[⟨3, 4, 180⟩, ⟨3, 5, 78⟩, ⟨3, 6, 93⟩, ⟨4, 5, 103⟩, ⟨4, 6, 75⟩, ⟨5, 6, 1⟩, ⟨0, 3, 98⟩, ⟨1, 3, 88⟩, ⟨0, 4, 90⟩, ⟨2, 4, 100⟩, ⟨0, 5, 16⟩, ⟨2, 5, 26⟩, ⟨0, 6, 28⟩, ⟨1, 6, 18⟩], triples := #[⟨0, 1, 2⟩] }
def er069_277 : Row := { vars := #[0, 37, 128, 431, 279], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 1000001, edges := #[⟨3, 4, 180⟩, ⟨0, 3, 244⟩, ⟨2, 3, 330⟩, ⟨0, 4, 404⟩, ⟨2, 4, 490⟩], triples := #[⟨0, 1, 2⟩] }
def er069_278 : Row := { vars := #[0, 153, 340, 132, 227], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 890244, edges := #[⟨3, 4, 402⟩, ⟨0, 3, 98⟩, ⟨2, 3, 276⟩, ⟨0, 4, 458⟩, ⟨2, 4, 186⟩], triples := #[⟨0, 1, 2⟩] }
def er069_279 : Row := { vars := #[0, 153, 340, 396, 56], coeff := #[1, 1, 1, 1, 1], bound := 2, weight := 109757, edges := #[⟨3, 4, 206⟩, ⟨0, 3, 276⟩, ⟨1, 3, 98⟩, ⟨0, 4, 186⟩, ⟨1, 4, 458⟩], triples := #[⟨0, 1, 2⟩] }
def er069_280 : Row := { vars := #[0, 185, 312, 46, 124, 118], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 1000000, edges := #[⟨3, 4, 41⟩, ⟨3, 5, 56⟩, ⟨4, 5, 169⟩, ⟨0, 3, 188⟩, ⟨2, 3, 298⟩, ⟨0, 4, 113⟩, ⟨2, 4, 289⟩, ⟨0, 5, 119⟩, ⟨2, 5, 278⟩], triples := #[⟨0, 1, 2⟩] }
def er069_281 : Row := { vars := #[0, 266, 374, 10, 80, 85], coeff := #[1, 1, 1, 1, 1, 1], bound := 2, weight := 500001, edges := #[⟨3, 4, 138⟩, ⟨3, 5, 163⟩, ⟨4, 5, 120⟩, ⟨0, 3, 17⟩, ⟨1, 3, 415⟩, ⟨0, 4, 158⟩, ⟨1, 4, 361⟩, ⟨0, 5, 150⟩, ⟨1, 5, 353⟩], triples := #[⟨0, 1, 2⟩] }
def er069_282 : Row := { vars := #[13], coeff := #[1], bound := 1, weight := 109757, edges := #[], triples := #[] }
def er069_283 : Row := { vars := #[14], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_284 : Row := { vars := #[22], coeff := #[1], bound := 1, weight := 890244, edges := #[], triples := #[] }
def er069_285 : Row := { vars := #[23], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_286 : Row := { vars := #[31], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er069_287 : Row := { vars := #[32], coeff := #[1], bound := 1, weight := 1000001, edges := #[], triples := #[] }
def er069_288 : Row := { vars := #[35], coeff := #[1], bound := 1, weight := 725610, edges := #[], triples := #[] }
def er069_289 : Row := { vars := #[36], coeff := #[1], bound := 1, weight := 890244, edges := #[], triples := #[] }
def er069_290 : Row := { vars := #[38], coeff := #[1], bound := 1, weight := 396342, edges := #[], triples := #[] }
def er069_291 : Row := { vars := #[43], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_292 : Row := { vars := #[47], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_293 : Row := { vars := #[54], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_294 : Row := { vars := #[62], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_295 : Row := { vars := #[75], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_296 : Row := { vars := #[88], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_297 : Row := { vars := #[89], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_298 : Row := { vars := #[96], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_299 : Row := { vars := #[100], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_300 : Row := { vars := #[107], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_301 : Row := { vars := #[111], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_302 : Row := { vars := #[115], coeff := #[1], bound := 1, weight := 1000001, edges := #[], triples := #[] }
def er069_303 : Row := { vars := #[145], coeff := #[1], bound := 1, weight := 500001, edges := #[], triples := #[] }
def er069_304 : Row := { vars := #[147], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_305 : Row := { vars := #[154], coeff := #[1], bound := 1, weight := 890244, edges := #[], triples := #[] }
def er069_306 : Row := { vars := #[160], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_307 : Row := { vars := #[183], coeff := #[1], bound := 1, weight := 335366, edges := #[], triples := #[] }
def er069_308 : Row := { vars := #[186], coeff := #[1], bound := 1, weight := 560976, edges := #[], triples := #[] }
def er069_309 : Row := { vars := #[188], coeff := #[1], bound := 1, weight := 500001, edges := #[], triples := #[] }
def er069_310 : Row := { vars := #[214], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_311 : Row := { vars := #[221], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er069_312 : Row := { vars := #[223], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_313 : Row := { vars := #[238], coeff := #[1], bound := 1, weight := 1, edges := #[], triples := #[] }
def er069_314 : Row := { vars := #[250], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_315 : Row := { vars := #[251], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_316 : Row := { vars := #[259], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_317 : Row := { vars := #[266], coeff := #[1], bound := 1, weight := 439025, edges := #[], triples := #[] }
def er069_318 : Row := { vars := #[274], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er069_319 : Row := { vars := #[275], coeff := #[1], bound := 1, weight := 390244, edges := #[], triples := #[] }
end HardyCapset20261020.Cert



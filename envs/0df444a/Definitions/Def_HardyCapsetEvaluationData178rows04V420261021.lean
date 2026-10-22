-- Prove2me | Definitions.Def_HardyCapsetEvaluationData178rows04V420261021
-- name    : HardyCapsetEvaluationData178rows04V420261021
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-21T03:16:46.608618+00:00
-- url     : https://prove2.me/theorems/352a72f6-9eeb-4700-98a5-742d1b9d4eaa
-- title:
--   HardyCapsetEvaluationData178rows04V420261021
-- statement:
--   Exact literal projections of the original certificate fields, for kernel-checked evaluation. Each use is linked to the original certificate by reflexivity; no new mathematical hypothesis is introduced.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetBooleanVerifier20261020
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace HardyCapset20261020.Cert
def er178_256 : Row := { vars := #[97], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_257 : Row := { vars := #[99], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_258 : Row := { vars := #[100], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_259 : Row := { vars := #[101], coeff := #[1], bound := 1, weight := 775177, edges := #[], triples := #[] }
def er178_260 : Row := { vars := #[102], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_261 : Row := { vars := #[103], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_262 : Row := { vars := #[120], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_263 : Row := { vars := #[121], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_264 : Row := { vars := #[122], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_265 : Row := { vars := #[123], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_266 : Row := { vars := #[126], coeff := #[1], bound := 1, weight := 675600, edges := #[], triples := #[] }
def er178_267 : Row := { vars := #[127], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_268 : Row := { vars := #[135], coeff := #[1], bound := 1, weight := 629902, edges := #[], triples := #[] }
def er178_269 : Row := { vars := #[136], coeff := #[1], bound := 1, weight := 357405, edges := #[], triples := #[] }
def er178_270 : Row := { vars := #[137], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_271 : Row := { vars := #[138], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_272 : Row := { vars := #[146], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_273 : Row := { vars := #[153], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_274 : Row := { vars := #[161], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_275 : Row := { vars := #[168], coeff := #[1], bound := 1, weight := 632441, edges := #[], triples := #[] }
def er178_276 : Row := { vars := #[176], coeff := #[1], bound := 1, weight := 738788, edges := #[], triples := #[] }
def er178_277 : Row := { vars := #[183], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_278 : Row := { vars := #[195], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_279 : Row := { vars := #[199], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_280 : Row := { vars := #[200], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_281 : Row := { vars := #[205], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_282 : Row := { vars := #[220], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_283 : Row := { vars := #[221], coeff := #[1], bound := 1, weight := 393230, edges := #[], triples := #[] }
def er178_284 : Row := { vars := #[226], coeff := #[1], bound := 1, weight := 997462, edges := #[], triples := #[] }
def er178_285 : Row := { vars := #[231], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_286 : Row := { vars := #[236], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_287 : Row := { vars := #[237], coeff := #[1], bound := 1, weight := 675600, edges := #[], triples := #[] }
def er178_288 : Row := { vars := #[242], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_289 : Row := { vars := #[243], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_290 : Row := { vars := #[245], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_291 : Row := { vars := #[246], coeff := #[1], bound := 1, weight := 172356, edges := #[], triples := #[] }
def er178_292 : Row := { vars := #[257], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_293 : Row := { vars := #[259], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_294 : Row := { vars := #[264], coeff := #[1], bound := 1, weight := 460085, edges := #[], triples := #[] }
def er178_295 : Row := { vars := #[265], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_296 : Row := { vars := #[266], coeff := #[1], bound := 1, weight := 741608, edges := #[], triples := #[] }
def er178_297 : Row := { vars := #[278], coeff := #[1], bound := 1, weight := 775177, edges := #[], triples := #[] }
def er178_298 : Row := { vars := #[279], coeff := #[1], bound := 1, weight := 917631, edges := #[], triples := #[] }
def er178_299 : Row := { vars := #[280], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_300 : Row := { vars := #[281], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_301 : Row := { vars := #[292], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_302 : Row := { vars := #[296], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_303 : Row := { vars := #[311], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_304 : Row := { vars := #[322], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_305 : Row := { vars := #[326], coeff := #[1], bound := 1, weight := 910015, edges := #[], triples := #[] }
def er178_306 : Row := { vars := #[330], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_307 : Row := { vars := #[331], coeff := #[1], bound := 1, weight := 910015, edges := #[], triples := #[] }
def er178_308 : Row := { vars := #[338], coeff := #[1], bound := 1, weight := 2539, edges := #[], triples := #[] }
def er178_309 : Row := { vars := #[341], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_310 : Row := { vars := #[342], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_311 : Row := { vars := #[348], coeff := #[1], bound := 1, weight := 375177, edges := #[], triples := #[] }
def er178_312 : Row := { vars := #[359], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_313 : Row := { vars := #[364], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_314 : Row := { vars := #[367], coeff := #[1], bound := 1, weight := 179972, edges := #[], triples := #[] }
def er178_315 : Row := { vars := #[368], coeff := #[1], bound := 1, weight := 804796, edges := #[], triples := #[] }
def er178_316 : Row := { vars := #[374], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_317 : Row := { vars := #[375], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
def er178_318 : Row := { vars := #[378], coeff := #[1], bound := 1, weight := 7617, edges := #[], triples := #[] }
def er178_319 : Row := { vars := #[379], coeff := #[1], bound := 1, weight := 1000000, edges := #[], triples := #[] }
end HardyCapset20261020.Cert



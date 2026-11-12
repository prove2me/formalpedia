-- Prove2me | Definitions.Def_OAIQ259US012
-- name    : OAIQ259US012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:09:48.221709+00:00
-- url     : https://prove2.me/theorems/b0f95561-6174-4b0e-9640-51fe75d755a0
-- title:
--   Definitions bundle OAIQ259US012 of the split of OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.UniversalTensorSquares.universal_tensor_square`, carved from OpenAI's openai/math development (OpenAI, *Universal Tensor Squares for Symmetric Groups (result family 205)*, OpenAI Math Release, September 24, 2026, result family 205, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1232 declarations of OpenAI's Lean: 1210 definitions, 13 instances and 9 theorems. The definitions and types are `OAI.UniversalTensorSquare.degreeP64`, `OAI.UniversalTensorSquare.degreePlan112_1`, `OAI.UniversalTensorSquare.degreePlan116_0`, `OAI.UniversalTensorSquare.degreePlan116_1`, `OAI.UniversalTensorSquare.degreePlan118_0`, `OAI.UniversalTensorSquare.degreePlan151_0`, `OAI.UniversalTensorSquare.degreePlan151_1`, `OAI.UniversalTensorSquare.degreePlan16_0`, `OAI.UniversalTensorSquare.degreePlan18_0`, `OAI.UniversalTensorSquare.degreePlan19_0`, `OAI.UniversalTensorSquare.degreePlan20_0`, `OAI.UniversalTensorSquare.degreePlan22_0`, `OAI.UniversalTensorSquare.degreePlan23_0`, `OAI.UniversalTensorSquare.degreePlan23_1`, `OAI.UniversalTensorSquare.degreePlan24_0`, `OAI.UniversalTensorSquare.degreePlan25_0`, `OAI.UniversalTensorSquare.degreePlan26_0`, `OAI.UniversalTensorSquare.degreePlan27_0`, `OAI.UniversalTensorSquare.degreePlan29_0`, `OAI.UniversalTensorSquare.degreePlan30_0`, `OAI.UniversalTensorSquare.degreePlan31_0`, `OAI.UniversalTensorSquare.degreePlan31_1`, `OAI.UniversalTensorSquare.degreePlan32_0`, `OAI.UniversalTensorSquare.degreePlan33_0`, `OAI.UniversalTensorSquare.degreePlan34_0`, `OAI.UniversalTensorSquare.degreePlan35_0`, `OAI.UniversalTensorSquare.degreePlan35_1`, `OAI.UniversalTensorSquare.degreePlan37_0`, `OAI.UniversalTensorSquare.degreePlan38_0`, `OAI.UniversalTensorSquare.degreePlan38_1`, `OAI.UniversalTensorSquare.degreePlan39_0`, `OAI.UniversalTensorSquare.degreePlan39_1`, `OAI.UniversalTensorSquare.degreePlan40_0`, `OAI.UniversalTensorSquare.degreePlan41_0`, `OAI.UniversalTensorSquare.degreePlan42_0`, `OAI.UniversalTensorSquare.degreePlan43_0`, `OAI.UniversalTensorSquare.degreePlan43_1`, `OAI.UniversalTensorSquare.degreePlan44_0`, `OAI.UniversalTensorSquare.degreePlan46_0`, `OAI.UniversalTensorSquare.degreePlan46_1` and 1170 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `UniversalSquare_Capacity_Intermediate`, `UniversalSquare_Capacity_RefinedExhaustion`, `UniversalSquare_Capacity_RegionExhaustion`, `UniversalSquare_Capacity_SentinelExhaustion`, `UniversalSquare_Contraction_RowCertificates`, `UniversalSquare_Finite_DegreeEight`, `UniversalSquare_Finite_DegreeFive`, `UniversalSquare_Finite_DegreePlans116`, `UniversalSquare_Finite_DegreePlans118`, `UniversalSquare_Finite_DegreePlans16`, `UniversalSquare_Finite_DegreePlans18`, `UniversalSquare_Finite_DegreePlans19`, `UniversalSquare_Finite_DegreePlans20`, `UniversalSquare_Finite_DegreePlans22`, `UniversalSquare_Finite_DegreePlans24`, `UniversalSquare_Finite_DegreePlans26`, `UniversalSquare_Finite_DegreePlans31`, `UniversalSquare_Finite_DegreePlans35`, `UniversalSquare_Finite_DegreePlans37`, `UniversalSquare_Finite_DegreePlans39`, `UniversalSquare_Finite_DegreePlans41`, `UniversalSquare_Finite_DegreePlans43`, `UniversalSquare_Finite_DegreePlans58`, `UniversalSquare_Finite_DegreePlans62`, `UniversalSquare_Finite_DegreePlans64`, `UniversalSquare_Finite_DegreePlans89`, `UniversalSquare_Finite_DegreeRegionData116`, `UniversalSquare_Finite_DegreeRegionData118`, `UniversalSquare_Finite_DegreeRegionData14`, `UniversalSquare_Finite_DegreeRegionData16`, `UniversalSquare_Finite_DegreeRegionData18`, `UniversalSquare_Finite_DegreeRegionData19`, `UniversalSquare_Finite_DegreeRegionData20`, `UniversalSquare_Finite_DegreeRegionData22`, `UniversalSquare_Finite_DegreeRegionData24`, `UniversalSquare_Finite_DegreeRegionData26`, `UniversalSquare_Finite_DegreeRegionData31`, `UniversalSquare_Finite_DegreeRegionData35`, `UniversalSquare_Finite_DegreeRegionData37`, `UniversalSquare_Finite_DegreeRegionData39`, `UniversalSquare_Finite_DegreeRegionData41`, `UniversalSquare_Finite_DegreeRegionData43`, `UniversalSquare_Finite_DegreeRegionData58`, `UniversalSquare_Finite_DegreeRegionData62`, `UniversalSquare_Finite_DegreeRegionData64`, `UniversalSquare_Finite_DegreeRegionData89`, `UniversalSquare_Finite_DegreeSeven`, `UniversalSquare_Finite_DegreeTreeData62`, `UniversalSquare_Finite_DegreeTreeData64`, `UniversalSquare_Finite_DegreeUnionStates24`, `UniversalSquare_Finite_DegreeUnionStates26`, `UniversalSquare_Finite_DegreeUnionStates31`, `UniversalSquare_Finite_DegreeUnionStates35`, `UniversalSquare_Finite_NumericalDegree112`, `UniversalSquare_Finite_NumericalDegree151`, `UniversalSquare_Finite_NumericalDegree23`, `UniversalSquare_Finite_NumericalDegree25`, `UniversalSquare_Finite_NumericalDegree27`, `UniversalSquare_Finite_NumericalDegree29`, `UniversalSquare_Finite_NumericalDegree30`, `UniversalSquare_Finite_NumericalDegree32`, `UniversalSquare_Finite_NumericalDegree33`, `UniversalSquare_Finite_NumericalDegree34`, `UniversalSquare_Finite_NumericalDegree38`, `UniversalSquare_Finite_NumericalDegree40`, `UniversalSquare_Finite_NumericalDegree42`, `UniversalSquare_Finite_NumericalDegree44`, `UniversalSquare_Finite_NumericalDegree46`, `UniversalSquare_Finite_NumericalDegree47`, `UniversalSquare_Finite_NumericalDegree48`, `UniversalSquare_Finite_NumericalDegree49`, `UniversalSquare_Finite_NumericalDegree50`, `UniversalSquare_Finite_NumericalDegree51`, `UniversalSquare_Finite_NumericalDegree52`, `UniversalSquare_Finite_NumericalDegree53`, `UniversalSquare_Finite_NumericalDegree54`, `UniversalSquare_Finite_NumericalDegree56`, `UniversalSquare_Finite_NumericalDegree57`, `UniversalSquare_Finite_NumericalDegree59`, `UniversalSquare_Finite_NumericalDegree60`, `UniversalSquare_Finite_NumericalDegree61`, `UniversalSquare_Finite_NumericalDegree63`, `UniversalSquare_Finite_PieriRows116`, `UniversalSquare_Finite_PieriRows118`, `UniversalSquare_Support_ConstrainedDiagrams`, `UniversalSquare_Support_ExceptionalFourteen`, `UniversalSquare_Support_FastRowCheck`, `UniversalSquare_Support_FiniteDiagrams`, `UniversalSquare_Support_NumericalSupport`, `UniversalSquare_Support_ResidualTrees`, `UniversalSquare_Support_RowSquareTools`.
--
--   **Imports.** It imports the bundles `OAIQ259US001`, `OAIQ259US002` and `OAIQ259US003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ259US021` and `OAIQ259US022`; the statements `OAI.UniversalTensorSquare.candidate_residual_pos`, `OAI.UniversalTensorSquare.degreeCheck116`, `OAI.UniversalTensorSquare.degreeCheck118`, `OAI.UniversalTensorSquare.degreeCheck151`, `OAI.UniversalTensorSquare.degreeCheck151_2_0`, `OAI.UniversalTensorSquare.degreeCheck151_2_1`, `OAI.UniversalTensorSquare.degreeCheck151_2_2`, `OAI.UniversalTensorSquare.degreeCheck151_2_3`, `OAI.UniversalTensorSquare.degreeCheck151_2_4`, `OAI.UniversalTensorSquare.degreeCheck151_3_0`, `OAI.UniversalTensorSquare.degreeCheck151_3_1`, `OAI.UniversalTensorSquare.degreeCheck151_3_2`, `OAI.UniversalTensorSquare.degreeCheck151_3_3`, `OAI.UniversalTensorSquare.degreeCheck151_3_4`, `OAI.UniversalTensorSquare.degreeCheck151_4_0`, `OAI.UniversalTensorSquare.degreeCheck151_4_1`, `OAI.UniversalTensorSquare.degreeCheck151_4_2`, `OAI.UniversalTensorSquare.degreeCheck151_4_3`, `OAI.UniversalTensorSquare.degreeCheck151_4_4`, `OAI.UniversalTensorSquare.degreeCheck24`, `OAI.UniversalTensorSquare.degreeCheck31`, `OAI.UniversalTensorSquare.degreeCheck33`, `OAI.UniversalTensorSquare.degreeCheck35`, `OAI.UniversalTensorSquare.degreeCheck37`, `OAI.UniversalTensorSquare.degreeDiagramRegionsChecked31`, `OAI.UniversalTensorSquare.degreeTree62_191All`, `OAI.UniversalTensorSquare.degreeTree62_193All`, `OAI.UniversalTensorSquare.degreeTree62_195All`, `OAI.UniversalTensorSquare.degreeTree62_196All`, `OAI.UniversalTensorSquare.degreeTree62_198All`, `OAI.UniversalTensorSquare.degreeTree62_199All`, `OAI.UniversalTensorSquare.degreeTree62_201All`, `OAI.UniversalTensorSquare.degreeTree62_205All`, `OAI.UniversalTensorSquare.degreeTree62_207All`, `OAI.UniversalTensorSquare.degreeTree62_209All`, `OAI.UniversalTensorSquare.degreeTree62_210All`, `OAI.UniversalTensorSquare.degreeTree62_211All`, `OAI.UniversalTensorSquare.degreeTree62_212All`, `OAI.UniversalTensorSquare.degreeTree62_213All`, `OAI.UniversalTensorSquare.degreeTree62_216All`, `OAI.UniversalTensorSquare.degreeTree62_217All`, `OAI.UniversalTensorSquare.degreeTree62_220All`, `OAI.UniversalTensorSquare.degreeTree62_221All`, `OAI.UniversalTensorSquare.degreeTree62_225All`, `OAI.UniversalTensorSquare.degreeTree62_226All`, `OAI.UniversalTensorSquare.degreeTree62_227All`, `OAI.UniversalTensorSquare.degreeTree62_229All`, `OAI.UniversalTensorSquare.degreeTree62_230All`, `OAI.UniversalTensorSquare.degreeTree62_232All`, `OAI.UniversalTensorSquare.degreeTree62_233All`, `OAI.UniversalTensorSquare.degreeTree62_235All`, `OAI.UniversalTensorSquare.degreeTree62_236All`, `OAI.UniversalTensorSquare.degreeTree62_238All`, `OAI.UniversalTensorSquare.degreeTree62_239All`, `OAI.UniversalTensorSquare.degreeTree62_240All`, `OAI.UniversalTensorSquare.degreeTree62_242All`, `OAI.UniversalTensorSquare.degreeTree62_246All`, `OAI.UniversalTensorSquare.degreeTree62_248All`, `OAI.UniversalTensorSquare.degreeTree62_249All`, `OAI.UniversalTensorSquare.degreeTree62_255All`, `OAI.UniversalTensorSquare.degreeTree62_256All`, `OAI.UniversalTensorSquare.degreeTree62_258All`, `OAI.UniversalTensorSquare.degreeTree62_259All`, `OAI.UniversalTensorSquare.degreeTree62_261All`, `OAI.UniversalTensorSquare.degreeTree62_262All`, `OAI.UniversalTensorSquare.degreeTree62_263All`, `OAI.UniversalTensorSquare.degreeTree62_266All`, `OAI.UniversalTensorSquare.degreeTree62_267All`, `OAI.UniversalTensorSquare.degreeTree62_268All`, `OAI.UniversalTensorSquare.degreeTree62_270All`, `OAI.UniversalTensorSquare.degreeTree62_271All`, `OAI.UniversalTensorSquare.degreeTree62_273All`, `OAI.UniversalTensorSquare.degreeTree62_274All`, `OAI.UniversalTensorSquare.degreeTree62_275All`, `OAI.UniversalTensorSquare.degreeTree62_276All`, `OAI.UniversalTensorSquare.degreeTree62_277All`, `OAI.UniversalTensorSquare.degreeTree62_279All`, `OAI.UniversalTensorSquare.degreeTree62_280All`, `OAI.UniversalTensorSquare.degreeTree62_283All`, `OAI.UniversalTensorSquare.degreeTree62_285All`, `OAI.UniversalTensorSquare.degreeTree62_287All`, `OAI.UniversalTensorSquare.degreeTree62_288All`, `OAI.UniversalTensorSquare.degreeTree62_290All`, `OAI.UniversalTensorSquare.degreeTree62_291All`, `OAI.UniversalTensorSquare.degreeTree62_293All`, `OAI.UniversalTensorSquare.degreeTree62_294All`, `OAI.UniversalTensorSquare.degreeTree62_297All`, `OAI.UniversalTensorSquare.degreeTree62_298All`, `OAI.UniversalTensorSquare.degreeTree62_300All`, `OAI.UniversalTensorSquare.degreeTree62_302All`, `OAI.UniversalTensorSquare.degreeTree62_304All`, `OAI.UniversalTensorSquare.degreeTree62_306All`, `OAI.UniversalTensorSquare.degreeTree62_307All`, `OAI.UniversalTensorSquare.degreeTree62_309All`, `OAI.UniversalTensorSquare.degreeTree62_310All`, `OAI.UniversalTensorSquare.degreeTree62_311All`, `OAI.UniversalTensorSquare.degreeTree62_313All`, `OAI.UniversalTensorSquare.degreeTree62_317All`, `OAI.UniversalTensorSquare.degreeTree62_318All`, `OAI.UniversalTensorSquare.degreeTree62_320All`, `OAI.UniversalTensorSquare.degreeTree62_322All`, `OAI.UniversalTensorSquare.degreeTree62_323All`, `OAI.UniversalTensorSquare.degreeTree62_326All`, `OAI.UniversalTensorSquare.degreeTree62_327All`, `OAI.UniversalTensorSquare.degreeTree62_328All`, `OAI.UniversalTensorSquare.degreeTree62_329All`, `OAI.UniversalTensorSquare.degreeTree62_330All`, `OAI.UniversalTensorSquare.degreeTree62_332All`, `OAI.UniversalTensorSquare.degreeTree62_336All`, `OAI.UniversalTensorSquare.degreeTree62_337All`, `OAI.UniversalTensorSquare.degreeTree62_339All`, `OAI.UniversalTensorSquare.degreeTree62_340All`, `OAI.UniversalTensorSquare.degreeTree62_341All`, `OAI.UniversalTensorSquare.degreeTree62_342All`, `OAI.UniversalTensorSquare.degreeTree62_344All`, `OAI.UniversalTensorSquare.degreeTree62_348All`, `OAI.UniversalTensorSquare.degreeTree62_349All`, `OAI.UniversalTensorSquare.degreeTree62_351All`, `OAI.UniversalTensorSquare.degreeTree62_352All`, `OAI.UniversalTensorSquare.degreeTree62_353All`, `OAI.UniversalTensorSquare.degreeTree62_355All`, `OAI.UniversalTensorSquare.degreeTree62_356All`, `OAI.UniversalTensorSquare.degreeTree62_357All`, `OAI.UniversalTensorSquare.degreeTree62_360All`, `OAI.UniversalTensorSquare.degreeTree62_361All`, `OAI.UniversalTensorSquare.degreeTree62_363All`, `OAI.UniversalTensorSquare.degreeTree62_364All`, `OAI.UniversalTensorSquare.degreeTree62_366All`, `OAI.UniversalTensorSquare.degreeTree62_367All`, `OAI.UniversalTensorSquare.degreeTree62_369All`, `OAI.UniversalTensorSquare.degreeTree62_371All`, `OAI.UniversalTensorSquare.degreeTree62_372All`, `OAI.UniversalTensorSquare.degreeTree62_373All`, `OAI.UniversalTensorSquare.degreeTree62_374All`, `OAI.UniversalTensorSquare.degreeTree62_375All`, `OAI.UniversalTensorSquare.degreeTree62_378All`, `OAI.UniversalTensorSquare.degreeTree62_380All`, `OAI.UniversalTensorSquare.degreeTree62_381All`, `OAI.UniversalTensorSquare.degreeTree62_382All`, `OAI.UniversalTensorSquare.degreeTree62_384All`, `OAI.UniversalTensorSquare.degreeTree62_385All`, `OAI.UniversalTensorSquare.degreeTree62_388All`, `OAI.UniversalTensorSquare.degreeTree62_389All`, `OAI.UniversalTensorSquare.degreeTree62_390All`, `OAI.UniversalTensorSquare.degreeTree62_393All`, `OAI.UniversalTensorSquare.degreeTree62_394All`, `OAI.UniversalTensorSquare.degreeTree62_395All`, `OAI.UniversalTensorSquare.degreeTree62_397All`, `OAI.UniversalTensorSquare.degreeTree62_402All`, `OAI.UniversalTensorSquare.degreeTree62_403All`, `OAI.UniversalTensorSquare.degreeTree62_404All`, `OAI.UniversalTensorSquare.degreeTree62_405All`, `OAI.UniversalTensorSquare.degreeTree62_406All`, `OAI.UniversalTensorSquare.degreeTree62_408All`, `OAI.UniversalTensorSquare.degreeTree62_409All`, `OAI.UniversalTensorSquare.degreeTree62_412All`, `OAI.UniversalTensorSquare.degreeTree62_413All`, `OAI.UniversalTensorSquare.degreeTree62_414All`, `OAI.UniversalTensorSquare.degreeTree62_415All`, `OAI.UniversalTensorSquare.degreeTree62_416All`, `OAI.UniversalTensorSquare.degreeTree62_420All`, `OAI.UniversalTensorSquare.degreeTree62_422All`, `OAI.UniversalTensorSquare.degreeTree62_423All`, `OAI.UniversalTensorSquare.degreeTree62_426All`, `OAI.UniversalTensorSquare.degreeTree62_427All`, `OAI.UniversalTensorSquare.degreeTree62_430All`, `OAI.UniversalTensorSquare.degreeTree62_434All`, `OAI.UniversalTensorSquare.degreeTree62_435All`, `OAI.UniversalTensorSquare.degreeTree62_436All`, `OAI.UniversalTensorSquare.degreeTree62_437All`, `OAI.UniversalTensorSquare.degreeTree62_438All`, `OAI.UniversalTensorSquare.degreeTree62_439All`, `OAI.UniversalTensorSquare.degreeTree62_444All`, `OAI.UniversalTensorSquare.degreeTree62_445All`, `OAI.UniversalTensorSquare.degreeTree62_449All`, `OAI.UniversalTensorSquare.degreeTree62_450All`, `OAI.UniversalTensorSquare.degreeTree62_452All`, `OAI.UniversalTensorSquare.degreeTree62_454All`, `OAI.UniversalTensorSquare.degreeTree62_456All`, `OAI.UniversalTensorSquare.degreeTree62_461All`, `OAI.UniversalTensorSquare.degreeTree62_462All`, `OAI.UniversalTensorSquare.degreeTree62_464All`, `OAI.UniversalTensorSquare.degreeTree62_465All`, `OAI.UniversalTensorSquare.degreeTree62_467All`, `OAI.UniversalTensorSquare.degreeTree62_469All`, `OAI.UniversalTensorSquare.degreeTree62_470All`, `OAI.UniversalTensorSquare.degreeTree62_471All`, `OAI.UniversalTensorSquare.degreeTree62_473All`, `OAI.UniversalTensorSquare.degreeTree62_474All`, `OAI.UniversalTensorSquare.degreeTree62_475All`, `OAI.UniversalTensorSquare.degreeTree62_476All`, `OAI.UniversalTensorSquare.degreeTree62_478All`, `OAI.UniversalTensorSquare.degreeTree62_479All`, `OAI.UniversalTensorSquare.degreeTree62_483All`, `OAI.UniversalTensorSquare.degreeTree62_485All`, `OAI.UniversalTensorSquare.degreeTree62_486All`, `OAI.UniversalTensorSquare.degreeTree62_487All`, `OAI.UniversalTensorSquare.degreeTree62_489All`, `OAI.UniversalTensorSquare.degreeTree62_490All`, `OAI.UniversalTensorSquare.degreeTree62_491All`, `OAI.UniversalTensorSquare.degreeTree62_494All`, `OAI.UniversalTensorSquare.degreeTree62_496All`, `OAI.UniversalTensorSquare.degreeTree62_497All`, `OAI.UniversalTensorSquare.degreeTree62_498All`, `OAI.UniversalTensorSquare.degreeTree62_499All`, `OAI.UniversalTensorSquare.degreeTree62_502All`, `OAI.UniversalTensorSquare.degreeTree62_503All`, `OAI.UniversalTensorSquare.degreeTree62_505All`, `OAI.UniversalTensorSquare.degreeTree62_507All`, `OAI.UniversalTensorSquare.degreeTree62_509All` and `OAI.UniversalTensorSquare.degreeTree64_0All`; the proofs of `OAI.UniversalTensorSquare.degreeCheck151`, `OAI.UniversalTensorSquare.degreeCheck151_2_0`, `OAI.UniversalTensorSquare.degreeCheck151_2_1`, `OAI.UniversalTensorSquare.degreeCheck151_2_2`, `OAI.UniversalTensorSquare.degreeCheck151_2_3`, `OAI.UniversalTensorSquare.degreeCheck151_2_4`, `OAI.UniversalTensorSquare.degreeCheck151_3_0`, `OAI.UniversalTensorSquare.degreeCheck151_3_1`, `OAI.UniversalTensorSquare.degreeCheck151_3_2`, `OAI.UniversalTensorSquare.degreeCheck151_3_3`, `OAI.UniversalTensorSquare.degreeCheck151_3_4`, `OAI.UniversalTensorSquare.degreeCheck151_4_0`, `OAI.UniversalTensorSquare.degreeCheck151_4_1`, `OAI.UniversalTensorSquare.degreeCheck151_4_2`, `OAI.UniversalTensorSquare.degreeCheck151_4_3`, `OAI.UniversalTensorSquare.degreeCheck151_4_4`, `OAI.UniversalTensorSquare.degreeCheck31`, `OAI.UniversalTensorSquare.degreeCheck33`, `OAI.UniversalTensorSquare.degreeTree39_117All`, `OAI.UniversalTensorSquare.degreeTree39_11All`, `OAI.UniversalTensorSquare.degreeTree39_17All`, `OAI.UniversalTensorSquare.degreeTree39_30All`, `OAI.UniversalTensorSquare.degreeTree39_84All`, `OAI.UniversalTensorSquare.degreeTree41_5All`, `OAI.UniversalTensorSquare.degreeTree41_8All`, `OAI.UniversalTensorSquare.degreeTree43_107All`, `OAI.UniversalTensorSquare.degreeTree43_120All`, `OAI.UniversalTensorSquare.degreeTree43_123All`, `OAI.UniversalTensorSquare.degreeTree43_126All`, `OAI.UniversalTensorSquare.degreeTree43_128All`, `OAI.UniversalTensorSquare.degreeTree43_140All`, `OAI.UniversalTensorSquare.degreeTree43_182All`, `OAI.UniversalTensorSquare.degreeTree43_183All`, `OAI.UniversalTensorSquare.degreeTree43_197All`, `OAI.UniversalTensorSquare.degreeTree43_201All`, `OAI.UniversalTensorSquare.degreeTree43_211All`, `OAI.UniversalTensorSquare.degreeTree43_221All`, `OAI.UniversalTensorSquare.degreeTree43_238All`, `OAI.UniversalTensorSquare.degreeTree43_257All`, `OAI.UniversalTensorSquare.degreeTree43_264All`, `OAI.UniversalTensorSquare.degreeTree43_280All`, `OAI.UniversalTensorSquare.degreeTree43_296All`, `OAI.UniversalTensorSquare.degreeTree43_298All`, `OAI.UniversalTensorSquare.degreeTree43_321All`, `OAI.UniversalTensorSquare.degreeTree43_382All`, `OAI.UniversalTensorSquare.degreeTree43_43All`, `OAI.UniversalTensorSquare.degreeTree43_493All`, `OAI.UniversalTensorSquare.degreeTree43_540All`, `OAI.UniversalTensorSquare.degreeTree43_56All`, `OAI.UniversalTensorSquare.degreeTree43_583All`, `OAI.UniversalTensorSquare.degreeTree43_585All`, `OAI.UniversalTensorSquare.degreeTree43_59All`, `OAI.UniversalTensorSquare.degreeTree43_645All`, `OAI.UniversalTensorSquare.degreeTree43_68All`, `OAI.UniversalTensorSquare.degreeTree43_77All`, `OAI.UniversalTensorSquare.degreeTree43_80All`, `OAI.UniversalTensorSquare.degreeTree43_82All`, `OAI.UniversalTensorSquare.degreeTree43_83All`, `OAI.UniversalTensorSquare.degreeTree43_85All`, `OAI.UniversalTensorSquare.degreeTree43_95All`, `OAI.UniversalTensorSquare.degreeTree43_97All`, `OAI.UniversalTensorSquare.degreeTree43_99All`, `OAI.UniversalTensorSquare.degreeTree62_1000All`, `OAI.UniversalTensorSquare.degreeTree62_1005All`, `OAI.UniversalTensorSquare.degreeTree62_1016All`, `OAI.UniversalTensorSquare.degreeTree62_107All`, `OAI.UniversalTensorSquare.degreeTree62_115All`, `OAI.UniversalTensorSquare.degreeTree62_140All`, `OAI.UniversalTensorSquare.degreeTree62_148All`, `OAI.UniversalTensorSquare.degreeTree62_166All`, `OAI.UniversalTensorSquare.degreeTree62_178All`, `OAI.UniversalTensorSquare.degreeTree62_195All`, `OAI.UniversalTensorSquare.degreeTree62_210All`, `OAI.UniversalTensorSquare.degreeTree62_212All`, `OAI.UniversalTensorSquare.degreeTree62_216All`, `OAI.UniversalTensorSquare.degreeTree62_220All`, `OAI.UniversalTensorSquare.degreeTree62_242All`, `OAI.UniversalTensorSquare.degreeTree62_275All`, `OAI.UniversalTensorSquare.degreeTree62_283All`, `OAI.UniversalTensorSquare.degreeTree62_298All`, `OAI.UniversalTensorSquare.degreeTree62_307All`, `OAI.UniversalTensorSquare.degreeTree62_317All`, `OAI.UniversalTensorSquare.degreeTree62_34All`, `OAI.UniversalTensorSquare.degreeTree62_38All`, `OAI.UniversalTensorSquare.degreeTree62_43All`, `OAI.UniversalTensorSquare.degreeTree62_44All`, `OAI.UniversalTensorSquare.degreeTree62_47All`, `OAI.UniversalTensorSquare.degreeTree62_505All`, `OAI.UniversalTensorSquare.degreeTree62_52All`, `OAI.UniversalTensorSquare.degreeTree62_576All`, `OAI.UniversalTensorSquare.degreeTree62_588All`, `OAI.UniversalTensorSquare.degreeTree62_59All`, `OAI.UniversalTensorSquare.degreeTree62_5All`, `OAI.UniversalTensorSquare.degreeTree62_667All`, `OAI.UniversalTensorSquare.degreeTree62_715All`, `OAI.UniversalTensorSquare.degreeTree62_719All`, `OAI.UniversalTensorSquare.degreeTree62_736All`, `OAI.UniversalTensorSquare.degreeTree62_777All`, `OAI.UniversalTensorSquare.degreeTree62_857All`, `OAI.UniversalTensorSquare.degreeTree62_891All`, `OAI.UniversalTensorSquare.degreeTree62_94All`, `OAI.UniversalTensorSquare.degreeTree62_968All`, `OAI.UniversalTensorSquare.degreeTree62_985All`, `OAI.UniversalTensorSquare.degree_pos151`, `OAI.UniversalTensorSquare.degree_pos32`, `OAI.UniversalTensorSquare.degree_pos33`, `OAI.UniversalTensorSquare.degree_pos34`, `OAI.UniversalTensorSquare.degree_pos44`, `OAI.UniversalTensorSquare.degree_pos48`, `OAI.UniversalTensorSquare.degree_pos52`, `OAI.UniversalTensorSquare.degree_pos53`, `OAI.UniversalTensorSquare.degree_pos56`, `OAI.UniversalTensorSquare.degree_pos59`, `OAI.UniversalTensorSquare.degree_pos60`, `OAI.UniversalTensorSquare.degree_pos61`, `OAI.UniversalTensorSquare.sg10044`, `OAI.UniversalTensorSquare.sg10099`, `OAI.UniversalTensorSquare.sg10211`, `OAI.UniversalTensorSquare.sg10214`, `OAI.UniversalTensorSquare.sg10215`, `OAI.UniversalTensorSquare.sg10218`, `OAI.UniversalTensorSquare.sg10219`, `OAI.UniversalTensorSquare.sg10220`, `OAI.UniversalTensorSquare.sg10221`, `OAI.UniversalTensorSquare.sg10222`, `OAI.UniversalTensorSquare.sg10223`, `OAI.UniversalTensorSquare.sg10224`, `OAI.UniversalTensorSquare.sg10225`, `OAI.UniversalTensorSquare.sg10226`, `OAI.UniversalTensorSquare.sg10227`, `OAI.UniversalTensorSquare.sg10228`, `OAI.UniversalTensorSquare.sg10229`, `OAI.UniversalTensorSquare.sg10230`, `OAI.UniversalTensorSquare.sg10236`, `OAI.UniversalTensorSquare.sg10240`, `OAI.UniversalTensorSquare.sg10242`, `OAI.UniversalTensorSquare.sg10243`, `OAI.UniversalTensorSquare.sg10244`, `OAI.UniversalTensorSquare.sg10268`, `OAI.UniversalTensorSquare.sg10271`, `OAI.UniversalTensorSquare.sg10273`, `OAI.UniversalTensorSquare.sg10279`, `OAI.UniversalTensorSquare.sg10280`, `OAI.UniversalTensorSquare.sg10283`, `OAI.UniversalTensorSquare.sg10287`, `OAI.UniversalTensorSquare.sg10288`, `OAI.UniversalTensorSquare.sg10291`, `OAI.UniversalTensorSquare.sg10292`, `OAI.UniversalTensorSquare.sg10293`, `OAI.UniversalTensorSquare.sg10294`, `OAI.UniversalTensorSquare.sg10295`, `OAI.UniversalTensorSquare.sg10296`, `OAI.UniversalTensorSquare.sg10297`, `OAI.UniversalTensorSquare.sg10298`, `OAI.UniversalTensorSquare.sg10299`, `OAI.UniversalTensorSquare.sg10300`, `OAI.UniversalTensorSquare.sg10301`, `OAI.UniversalTensorSquare.sg10302`, `OAI.UniversalTensorSquare.sg10303`, `OAI.UniversalTensorSquare.sg10304`, `OAI.UniversalTensorSquare.sg10305`, `OAI.UniversalTensorSquare.sg10306`, `OAI.UniversalTensorSquare.sg10307`, `OAI.UniversalTensorSquare.sg10311`, `OAI.UniversalTensorSquare.sg10315`, `OAI.UniversalTensorSquare.sg10316`, `OAI.UniversalTensorSquare.sg10318`, `OAI.UniversalTensorSquare.sg10319`, `OAI.UniversalTensorSquare.sg10351`, `OAI.UniversalTensorSquare.sg10364`, `OAI.UniversalTensorSquare.sg10368`, `OAI.UniversalTensorSquare.sg10369`, `OAI.UniversalTensorSquare.sg10370`, `OAI.UniversalTensorSquare.sg10373`, `OAI.UniversalTensorSquare.sg10375`, `OAI.UniversalTensorSquare.sg10377`, `OAI.UniversalTensorSquare.sg10379`, `OAI.UniversalTensorSquare.sg10381`, `OAI.UniversalTensorSquare.sg10387`, `OAI.UniversalTensorSquare.sg10388`, `OAI.UniversalTensorSquare.sg10389`, `OAI.UniversalTensorSquare.sg10390`, `OAI.UniversalTensorSquare.sg10391`, `OAI.UniversalTensorSquare.sg10392`, `OAI.UniversalTensorSquare.sg10393`, `OAI.UniversalTensorSquare.sg10394`, `OAI.UniversalTensorSquare.sg10395`, `OAI.UniversalTensorSquare.sg10396`, `OAI.UniversalTensorSquare.sg10397`, `OAI.UniversalTensorSquare.sg10398`, `OAI.UniversalTensorSquare.sg10399`, `OAI.UniversalTensorSquare.sg10400`, `OAI.UniversalTensorSquare.sg10401`, `OAI.UniversalTensorSquare.sg10402`, `OAI.UniversalTensorSquare.sg10403`, `OAI.UniversalTensorSquare.sg10405`, `OAI.UniversalTensorSquare.sg10406`, `OAI.UniversalTensorSquare.sg10407`, `OAI.UniversalTensorSquare.sg10408`, `OAI.UniversalTensorSquare.sg10409`, `OAI.UniversalTensorSquare.sg10410`, `OAI.UniversalTensorSquare.sg10472`, `OAI.UniversalTensorSquare.sg10475`, `OAI.UniversalTensorSquare.sg10476`, `OAI.UniversalTensorSquare.sg10479`, `OAI.UniversalTensorSquare.sg10480`, `OAI.UniversalTensorSquare.sg10488`, `OAI.UniversalTensorSquare.sg10489`, `OAI.UniversalTensorSquare.sg10491`, `OAI.UniversalTensorSquare.sg10492`, `OAI.UniversalTensorSquare.sg10494`, `OAI.UniversalTensorSquare.sg10495`, `OAI.UniversalTensorSquare.sg10498`, `OAI.UniversalTensorSquare.sg10500`, `OAI.UniversalTensorSquare.sg10501`, `OAI.UniversalTensorSquare.sg10537`, `OAI.UniversalTensorSquare.sg10624`, `OAI.UniversalTensorSquare.sg10634`, `OAI.UniversalTensorSquare.sg10639`, `OAI.UniversalTensorSquare.sg10664`, `OAI.UniversalTensorSquare.sg10666`, `OAI.UniversalTensorSquare.sg10676`, `OAI.UniversalTensorSquare.sg10680`, `OAI.UniversalTensorSquare.sg10686`, `OAI.UniversalTensorSquare.sg10689`, `OAI.UniversalTensorSquare.sg10843`, `OAI.UniversalTensorSquare.sg10911`, `OAI.UniversalTensorSquare.sg10916`, `OAI.UniversalTensorSquare.sg10918`, `OAI.UniversalTensorSquare.sg10932`, `OAI.UniversalTensorSquare.sg10946`, `OAI.UniversalTensorSquare.sg10949`, `OAI.UniversalTensorSquare.sg10963`, `OAI.UniversalTensorSquare.sg10972`, `OAI.UniversalTensorSquare.sg10977`, `OAI.UniversalTensorSquare.sg10980`, `OAI.UniversalTensorSquare.sg10981`, `OAI.UniversalTensorSquare.sg10984`, `OAI.UniversalTensorSquare.sg11010`, `OAI.UniversalTensorSquare.sg11208`, `OAI.UniversalTensorSquare.sg11209`, `OAI.UniversalTensorSquare.sg11210`, `OAI.UniversalTensorSquare.sg11212`, `OAI.UniversalTensorSquare.sg11213`, `OAI.UniversalTensorSquare.sg11215`, `OAI.UniversalTensorSquare.sg11226`, `OAI.UniversalTensorSquare.sg11227`, `OAI.UniversalTensorSquare.sg11228`, `OAI.UniversalTensorSquare.sg11229`, `OAI.UniversalTensorSquare.sg11230`, `OAI.UniversalTensorSquare.sg11231`, `OAI.UniversalTensorSquare.sg11232`, `OAI.UniversalTensorSquare.sg11233`, `OAI.UniversalTensorSquare.sg11234`, `OAI.UniversalTensorSquare.sg11278`, `OAI.UniversalTensorSquare.sg11279`, `OAI.UniversalTensorSquare.sg11280`, `OAI.UniversalTensorSquare.sg11304`, `OAI.UniversalTensorSquare.sg11307`, `OAI.UniversalTensorSquare.sg11496`, `OAI.UniversalTensorSquare.sg11497`, `OAI.UniversalTensorSquare.sg11498`, `OAI.UniversalTensorSquare.sg11499`, `OAI.UniversalTensorSquare.sg11500`, `OAI.UniversalTensorSquare.sg11501`, `OAI.UniversalTensorSquare.sg11502`, `OAI.UniversalTensorSquare.sg1162`, `OAI.UniversalTensorSquare.sg1169`, `OAI.UniversalTensorSquare.sg11814`, `OAI.UniversalTensorSquare.sg11842`, `OAI.UniversalTensorSquare.sg11843`, `OAI.UniversalTensorSquare.sg11848`, `OAI.UniversalTensorSquare.sg11852`, `OAI.UniversalTensorSquare.sg11855`, `OAI.UniversalTensorSquare.sg11868`, `OAI.UniversalTensorSquare.sg11869`, `OAI.UniversalTensorSquare.sg11903`, `OAI.UniversalTensorSquare.sg11925`, `OAI.UniversalTensorSquare.sg11929`, `OAI.UniversalTensorSquare.sg11930`, `OAI.UniversalTensorSquare.sg11942`, `OAI.UniversalTensorSquare.sg11951`, `OAI.UniversalTensorSquare.sg11971`, `OAI.UniversalTensorSquare.sg11972`, `OAI.UniversalTensorSquare.sg11973`, `OAI.UniversalTensorSquare.sg11980`, `OAI.UniversalTensorSquare.sg11985`, `OAI.UniversalTensorSquare.sg11989`, `OAI.UniversalTensorSquare.sg11990`, `OAI.UniversalTensorSquare.sg11992`, `OAI.UniversalTensorSquare.sg12001`, `OAI.UniversalTensorSquare.sg12003`, `OAI.UniversalTensorSquare.sg12007`, `OAI.UniversalTensorSquare.sg12015`, `OAI.UniversalTensorSquare.sg12023`, `OAI.UniversalTensorSquare.sg12033`, `OAI.UniversalTensorSquare.sg12037`, `OAI.UniversalTensorSquare.sg12040`, `OAI.UniversalTensorSquare.sg12042`, `OAI.UniversalTensorSquare.sg12048`, `OAI.UniversalTensorSquare.sg12052`, `OAI.UniversalTensorSquare.sg12059`, `OAI.UniversalTensorSquare.sg12060`, `OAI.UniversalTensorSquare.sg12081`, `OAI.UniversalTensorSquare.sg12082`, `OAI.UniversalTensorSquare.sg12101`, `OAI.UniversalTensorSquare.sg12102`, `OAI.UniversalTensorSquare.sg12119`, `OAI.UniversalTensorSquare.sg12132`, `OAI.UniversalTensorSquare.sg12160`, `OAI.UniversalTensorSquare.sg12164`, `OAI.UniversalTensorSquare.sg12180`, `OAI.UniversalTensorSquare.sg12184`, `OAI.UniversalTensorSquare.sg12185`, `OAI.UniversalTensorSquare.sg12187`, `OAI.UniversalTensorSquare.sg12223`, `OAI.UniversalTensorSquare.sg12232`, `OAI.UniversalTensorSquare.sg12245`, `OAI.UniversalTensorSquare.sg12251`, `OAI.UniversalTensorSquare.sg12258`, `OAI.UniversalTensorSquare.sg12293`, `OAI.UniversalTensorSquare.sg12323`, `OAI.UniversalTensorSquare.sg12329`, `OAI.UniversalTensorSquare.sg12418`, `OAI.UniversalTensorSquare.sg12691`, `OAI.UniversalTensorSquare.sg12702`, `OAI.UniversalTensorSquare.sg12960`, `OAI.UniversalTensorSquare.sg12966`, `OAI.UniversalTensorSquare.sg12971`, `OAI.UniversalTensorSquare.sg13084`, `OAI.UniversalTensorSquare.sg13104`, `OAI.UniversalTensorSquare.sg13121`, `OAI.UniversalTensorSquare.sg13141`, `OAI.UniversalTensorSquare.sg13305`, `OAI.UniversalTensorSquare.sg13307`, `OAI.UniversalTensorSquare.sg13353`, `OAI.UniversalTensorSquare.sg13354`, `OAI.UniversalTensorSquare.sg13363`, `OAI.UniversalTensorSquare.sg13416`, `OAI.UniversalTensorSquare.sg13475`, `OAI.UniversalTensorSquare.sg13480`, `OAI.UniversalTensorSquare.sg14235`, `OAI.UniversalTensorSquare.sg14296`, `OAI.UniversalTensorSquare.sg14386`, `OAI.UniversalTensorSquare.sg14546`, `OAI.UniversalTensorSquare.sg14640`, `OAI.UniversalTensorSquare.sg14756`, `OAI.UniversalTensorSquare.sg14762`, `OAI.UniversalTensorSquare.sg14763`, `OAI.UniversalTensorSquare.sg14812`, `OAI.UniversalTensorSquare.sg14816`, `OAI.UniversalTensorSquare.sg15223`, `OAI.UniversalTensorSquare.sg15646`, `OAI.UniversalTensorSquare.sg15653`, `OAI.UniversalTensorSquare.sg15672`, `OAI.UniversalTensorSquare.sg15756`, `OAI.UniversalTensorSquare.sg15886`, `OAI.UniversalTensorSquare.sg15936`, `OAI.UniversalTensorSquare.sg1608`, `OAI.UniversalTensorSquare.sg16165`, `OAI.UniversalTensorSquare.sg16341`, `OAI.UniversalTensorSquare.sg16364`, `OAI.UniversalTensorSquare.sg16379`, `OAI.UniversalTensorSquare.sg1638`, `OAI.UniversalTensorSquare.sg1639`, `OAI.UniversalTensorSquare.sg16731`, `OAI.UniversalTensorSquare.sg17146`, `OAI.UniversalTensorSquare.sg17188`, `OAI.UniversalTensorSquare.sg17197`, `OAI.UniversalTensorSquare.sg17265`, `OAI.UniversalTensorSquare.sg17298`, `OAI.UniversalTensorSquare.sg17299`, `OAI.UniversalTensorSquare.sg17341`, `OAI.UniversalTensorSquare.sg17342`, `OAI.UniversalTensorSquare.sg17345`, `OAI.UniversalTensorSquare.sg17475`, `OAI.UniversalTensorSquare.sg17542`, `OAI.UniversalTensorSquare.sg17688`, `OAI.UniversalTensorSquare.sg17754`, `OAI.UniversalTensorSquare.sg18274`, `OAI.UniversalTensorSquare.sg18703`, `OAI.UniversalTensorSquare.sg18762`, `OAI.UniversalTensorSquare.sg18846`, `OAI.UniversalTensorSquare.sg18971`, `OAI.UniversalTensorSquare.sg18974`, `OAI.UniversalTensorSquare.sg19115`, `OAI.UniversalTensorSquare.sg19130`, `OAI.UniversalTensorSquare.sg19133`, `OAI.UniversalTensorSquare.sg19153`, `OAI.UniversalTensorSquare.sg19171`, `OAI.UniversalTensorSquare.sg19176`, `OAI.UniversalTensorSquare.sg19321`, `OAI.UniversalTensorSquare.sg19574`, `OAI.UniversalTensorSquare.sg19623`, `OAI.UniversalTensorSquare.sg19628`, `OAI.UniversalTensorSquare.sg19635`, `OAI.UniversalTensorSquare.sg19709`, `OAI.UniversalTensorSquare.sg19710`, `OAI.UniversalTensorSquare.sg20306`, `OAI.UniversalTensorSquare.sg20523`, `OAI.UniversalTensorSquare.sg20588`, `OAI.UniversalTensorSquare.sg20660`, `OAI.UniversalTensorSquare.sg20661`, `OAI.UniversalTensorSquare.sg20674`, `OAI.UniversalTensorSquare.sg20675`, `OAI.UniversalTensorSquare.sg20676`, `OAI.UniversalTensorSquare.sg20677`, `OAI.UniversalTensorSquare.sg20680`, `OAI.UniversalTensorSquare.sg20682`, `OAI.UniversalTensorSquare.sg20758`, `OAI.UniversalTensorSquare.sg20787`, `OAI.UniversalTensorSquare.sg20788`, `OAI.UniversalTensorSquare.sg21085`, `OAI.UniversalTensorSquare.sg21086`, `OAI.UniversalTensorSquare.sg21087`, `OAI.UniversalTensorSquare.sg21180`, `OAI.UniversalTensorSquare.sg2132`, `OAI.UniversalTensorSquare.sg21349`, `OAI.UniversalTensorSquare.sg21351`, `OAI.UniversalTensorSquare.sg21356`, `OAI.UniversalTensorSquare.sg21359`, `OAI.UniversalTensorSquare.sg21401`, `OAI.UniversalTensorSquare.sg21402`, `OAI.UniversalTensorSquare.sg21405`, `OAI.UniversalTensorSquare.sg21406`, `OAI.UniversalTensorSquare.sg21410`, `OAI.UniversalTensorSquare.sg21482`, `OAI.UniversalTensorSquare.sg21502`, `OAI.UniversalTensorSquare.sg21505`, `OAI.UniversalTensorSquare.sg21516`, `OAI.UniversalTensorSquare.sg21557`, `OAI.UniversalTensorSquare.sg21565`, `OAI.UniversalTensorSquare.sg21596`, `OAI.UniversalTensorSquare.sg21607`, `OAI.UniversalTensorSquare.sg21671`, `OAI.UniversalTensorSquare.sg21689`, `OAI.UniversalTensorSquare.sg21697`, `OAI.UniversalTensorSquare.sg21701`, `OAI.UniversalTensorSquare.sg21706`, `OAI.UniversalTensorSquare.sg21707`, `OAI.UniversalTensorSquare.sg21710`, `OAI.UniversalTensorSquare.sg21712`, `OAI.UniversalTensorSquare.sg21716`, `OAI.UniversalTensorSquare.sg21737`, `OAI.UniversalTensorSquare.sg21745`, `OAI.UniversalTensorSquare.sg21748`, `OAI.UniversalTensorSquare.sg21757`, `OAI.UniversalTensorSquare.sg21763`, `OAI.UniversalTensorSquare.sg21766`, `OAI.UniversalTensorSquare.sg21772`, `OAI.UniversalTensorSquare.sg21773`, `OAI.UniversalTensorSquare.sg21777`, `OAI.UniversalTensorSquare.sg21778`, `OAI.UniversalTensorSquare.sg21779`, `OAI.UniversalTensorSquare.sg21782`, `OAI.UniversalTensorSquare.sg21784`, `OAI.UniversalTensorSquare.sg21785`, `OAI.UniversalTensorSquare.sg21789`, `OAI.UniversalTensorSquare.sg21790`, `OAI.UniversalTensorSquare.sg21791`, `OAI.UniversalTensorSquare.sg21793`, `OAI.UniversalTensorSquare.sg21794`, `OAI.UniversalTensorSquare.sg21796`, `OAI.UniversalTensorSquare.sg21801`, `OAI.UniversalTensorSquare.sg21803`, `OAI.UniversalTensorSquare.sg21806`, `OAI.UniversalTensorSquare.sg21810`, `OAI.UniversalTensorSquare.sg21812`, `OAI.UniversalTensorSquare.sg21814`, `OAI.UniversalTensorSquare.sg21817`, `OAI.UniversalTensorSquare.sg21819`, `OAI.UniversalTensorSquare.sg21821`, `OAI.UniversalTensorSquare.sg21823`, `OAI.UniversalTensorSquare.sg21829`, `OAI.UniversalTensorSquare.sg21833`, `OAI.UniversalTensorSquare.sg21835`, `OAI.UniversalTensorSquare.sg21837`, `OAI.UniversalTensorSquare.sg21839`, `OAI.UniversalTensorSquare.sg21870`, `OAI.UniversalTensorSquare.sg21878`, `OAI.UniversalTensorSquare.sg21880`, `OAI.UniversalTensorSquare.sg21883`, `OAI.UniversalTensorSquare.sg21884`, `OAI.UniversalTensorSquare.sg21887`, `OAI.UniversalTensorSquare.sg21888`, `OAI.UniversalTensorSquare.sg21897`, `OAI.UniversalTensorSquare.sg21900`, `OAI.UniversalTensorSquare.sg21901`, `OAI.UniversalTensorSquare.sg21902`, `OAI.UniversalTensorSquare.sg21905`, `OAI.UniversalTensorSquare.sg21907`, `OAI.UniversalTensorSquare.sg21908`, `OAI.UniversalTensorSquare.sg21909`, `OAI.UniversalTensorSquare.sg21911`, `OAI.UniversalTensorSquare.sg21913`, `OAI.UniversalTensorSquare.sg21915`, `OAI.UniversalTensorSquare.sg21918`, `OAI.UniversalTensorSquare.sg21920`, `OAI.UniversalTensorSquare.sg21921`, `OAI.UniversalTensorSquare.sg21922`, `OAI.UniversalTensorSquare.sg21923`, `OAI.UniversalTensorSquare.sg21924`, `OAI.UniversalTensorSquare.sg21928`, `OAI.UniversalTensorSquare.sg21930`, `OAI.UniversalTensorSquare.sg21931`, `OAI.UniversalTensorSquare.sg21934`, `OAI.UniversalTensorSquare.sg21936`, `OAI.UniversalTensorSquare.sg21938`, `OAI.UniversalTensorSquare.sg21940`, `OAI.UniversalTensorSquare.sg21942`, `OAI.UniversalTensorSquare.sg21944`, `OAI.UniversalTensorSquare.sg21947`, `OAI.UniversalTensorSquare.sg21952`, `OAI.UniversalTensorSquare.sg21955`, `OAI.UniversalTensorSquare.sg21956`, `OAI.UniversalTensorSquare.sg21957`, `OAI.UniversalTensorSquare.sg21958`, `OAI.UniversalTensorSquare.sg21959`, `OAI.UniversalTensorSquare.sg21960`, `OAI.UniversalTensorSquare.sg21962`, `OAI.UniversalTensorSquare.sg21963`, `OAI.UniversalTensorSquare.sg21967`, `OAI.UniversalTensorSquare.sg21968`, `OAI.UniversalTensorSquare.sg21969`, `OAI.UniversalTensorSquare.sg21972`, `OAI.UniversalTensorSquare.sg21973`, `OAI.UniversalTensorSquare.sg21974`, `OAI.UniversalTensorSquare.sg21975`, `OAI.UniversalTensorSquare.sg21982`, `OAI.UniversalTensorSquare.sg21983`, `OAI.UniversalTensorSquare.sg21985`, `OAI.UniversalTensorSquare.sg21987`, `OAI.UniversalTensorSquare.sg21989`, `OAI.UniversalTensorSquare.sg21992`, `OAI.UniversalTensorSquare.sg21994`, `OAI.UniversalTensorSquare.sg21995`, `OAI.UniversalTensorSquare.sg21997`, `OAI.UniversalTensorSquare.sg22000`, `OAI.UniversalTensorSquare.sg22003`, `OAI.UniversalTensorSquare.sg22005`, `OAI.UniversalTensorSquare.sg22006`, `OAI.UniversalTensorSquare.sg22008`, `OAI.UniversalTensorSquare.sg22009`, `OAI.UniversalTensorSquare.sg22011`, `OAI.UniversalTensorSquare.sg22012`, `OAI.UniversalTensorSquare.sg22015`, `OAI.UniversalTensorSquare.sg22018`, `OAI.UniversalTensorSquare.sg22021`, `OAI.UniversalTensorSquare.sg22022`, `OAI.UniversalTensorSquare.sg22031`, `OAI.UniversalTensorSquare.sg22035`, `OAI.UniversalTensorSquare.sg22037`, `OAI.UniversalTensorSquare.sg22038`, `OAI.UniversalTensorSquare.sg22040`, `OAI.UniversalTensorSquare.sg22043`, `OAI.UniversalTensorSquare.sg22046`, `OAI.UniversalTensorSquare.sg22049`, `OAI.UniversalTensorSquare.sg22050`, `OAI.UniversalTensorSquare.sg22052`, `OAI.UniversalTensorSquare.sg22053`, `OAI.UniversalTensorSquare.sg22057`, `OAI.UniversalTensorSquare.sg22059`, `OAI.UniversalTensorSquare.sg22061`, `OAI.UniversalTensorSquare.sg22063`, `OAI.UniversalTensorSquare.sg22065`, `OAI.UniversalTensorSquare.sg22066`, `OAI.UniversalTensorSquare.sg22067`, `OAI.UniversalTensorSquare.sg22068`, `OAI.UniversalTensorSquare.sg22069`, `OAI.UniversalTensorSquare.sg22072`, `OAI.UniversalTensorSquare.sg22073`, `OAI.UniversalTensorSquare.sg22074`, `OAI.UniversalTensorSquare.sg22075`, `OAI.UniversalTensorSquare.sg22076`, `OAI.UniversalTensorSquare.sg22079`, `OAI.UniversalTensorSquare.sg22080`, `OAI.UniversalTensorSquare.sg22082`, `OAI.UniversalTensorSquare.sg22088`, `OAI.UniversalTensorSquare.sg22101`, `OAI.UniversalTensorSquare.sg22104`, `OAI.UniversalTensorSquare.sg22118`, `OAI.UniversalTensorSquare.sg22121`, `OAI.UniversalTensorSquare.sg22122`, `OAI.UniversalTensorSquare.sg22151`, `OAI.UniversalTensorSquare.sg22158`, `OAI.UniversalTensorSquare.sg22159`, `OAI.UniversalTensorSquare.sg22163`, `OAI.UniversalTensorSquare.sg22168`, `OAI.UniversalTensorSquare.sg22171`, `OAI.UniversalTensorSquare.sg22174`, `OAI.UniversalTensorSquare.sg22195`, `OAI.UniversalTensorSquare.sg22196`, `OAI.UniversalTensorSquare.sg22198`, `OAI.UniversalTensorSquare.sg22199`, `OAI.UniversalTensorSquare.sg22200`, `OAI.UniversalTensorSquare.sg22201`, `OAI.UniversalTensorSquare.sg22216`, `OAI.UniversalTensorSquare.sg22219`, `OAI.UniversalTensorSquare.sg22225`, `OAI.UniversalTensorSquare.sg22231`, `OAI.UniversalTensorSquare.sg22233`, `OAI.UniversalTensorSquare.sg22234`, `OAI.UniversalTensorSquare.sg22238`, `OAI.UniversalTensorSquare.sg22239`, `OAI.UniversalTensorSquare.sg22243`, `OAI.UniversalTensorSquare.sg22245`, `OAI.UniversalTensorSquare.sg22248`, `OAI.UniversalTensorSquare.sg22250`, `OAI.UniversalTensorSquare.sg22251`, `OAI.UniversalTensorSquare.sg22253`, `OAI.UniversalTensorSquare.sg22255`, `OAI.UniversalTensorSquare.sg22256`, `OAI.UniversalTensorSquare.sg22261`, `OAI.UniversalTensorSquare.sg22266`, `OAI.UniversalTensorSquare.sg22267`, `OAI.UniversalTensorSquare.sg22270`, `OAI.UniversalTensorSquare.sg22271`, `OAI.UniversalTensorSquare.sg22272`, `OAI.UniversalTensorSquare.sg22278`, `OAI.UniversalTensorSquare.sg22279`, `OAI.UniversalTensorSquare.sg22282`, `OAI.UniversalTensorSquare.sg22283`, `OAI.UniversalTensorSquare.sg22284`, `OAI.UniversalTensorSquare.sg22285`, `OAI.UniversalTensorSquare.sg22290`, `OAI.UniversalTensorSquare.sg22291`, `OAI.UniversalTensorSquare.sg22305`, `OAI.UniversalTensorSquare.sg22308`, `OAI.UniversalTensorSquare.sg22310`, `OAI.UniversalTensorSquare.sg22333`, `OAI.UniversalTensorSquare.sg22336`, `OAI.UniversalTensorSquare.sg22342`, `OAI.UniversalTensorSquare.sg22346`, `OAI.UniversalTensorSquare.sg22347`, `OAI.UniversalTensorSquare.sg22348`, `OAI.UniversalTensorSquare.sg22349`, `OAI.UniversalTensorSquare.sg22351`, `OAI.UniversalTensorSquare.sg22353`, `OAI.UniversalTensorSquare.sg22355`, `OAI.UniversalTensorSquare.sg22361`, `OAI.UniversalTensorSquare.sg22363`, `OAI.UniversalTensorSquare.sg22364`, `OAI.UniversalTensorSquare.sg22365`, `OAI.UniversalTensorSquare.sg22366`, `OAI.UniversalTensorSquare.sg22370`, `OAI.UniversalTensorSquare.sg22374`, `OAI.UniversalTensorSquare.sg22378`, `OAI.UniversalTensorSquare.sg22380`, `OAI.UniversalTensorSquare.sg22381`, `OAI.UniversalTensorSquare.sg22383`, `OAI.UniversalTensorSquare.sg22384`, `OAI.UniversalTensorSquare.sg22385`, `OAI.UniversalTensorSquare.sg22386`, `OAI.UniversalTensorSquare.sg22399`, `OAI.UniversalTensorSquare.sg22400`, `OAI.UniversalTensorSquare.sg22406`, `OAI.UniversalTensorSquare.sg22411`, `OAI.UniversalTensorSquare.sg22412`, `OAI.UniversalTensorSquare.sg22418`, `OAI.UniversalTensorSquare.sg22420`, `OAI.UniversalTensorSquare.sg22499`, `OAI.UniversalTensorSquare.sg22567`, `OAI.UniversalTensorSquare.sg22584`, `OAI.UniversalTensorSquare.sg22586`, `OAI.UniversalTensorSquare.sg22592`, `OAI.UniversalTensorSquare.sg22646`, `OAI.UniversalTensorSquare.sg22704`, `OAI.UniversalTensorSquare.sg22708`, `OAI.UniversalTensorSquare.sg22716`, `OAI.UniversalTensorSquare.sg22731`, `OAI.UniversalTensorSquare.sg22761`, `OAI.UniversalTensorSquare.sg22778`, `OAI.UniversalTensorSquare.sg22786`, `OAI.UniversalTensorSquare.sg22800`, `OAI.UniversalTensorSquare.sg22803`, `OAI.UniversalTensorSquare.sg22811`, `OAI.UniversalTensorSquare.sg22821`, `OAI.UniversalTensorSquare.sg22823`, `OAI.UniversalTensorSquare.sg22842`, `OAI.UniversalTensorSquare.sg22845`, `OAI.UniversalTensorSquare.sg22851`, `OAI.UniversalTensorSquare.sg22857`, `OAI.UniversalTensorSquare.sg22867`, `OAI.UniversalTensorSquare.sg22881`, `OAI.UniversalTensorSquare.sg22882`, `OAI.UniversalTensorSquare.sg22884`, `OAI.UniversalTensorSquare.sg22890`, `OAI.UniversalTensorSquare.sg22899`, `OAI.UniversalTensorSquare.sg22900`, `OAI.UniversalTensorSquare.sg22914`, `OAI.UniversalTensorSquare.sg22917`, `OAI.UniversalTensorSquare.sg22922`, `OAI.UniversalTensorSquare.sg22941`, `OAI.UniversalTensorSquare.sg22943`, `OAI.UniversalTensorSquare.sg22955`, `OAI.UniversalTensorSquare.sg22976`, `OAI.UniversalTensorSquare.sg22977`, `OAI.UniversalTensorSquare.sg22983`, `OAI.UniversalTensorSquare.sg23000`, `OAI.UniversalTensorSquare.sg23021`, `OAI.UniversalTensorSquare.sg23024`, `OAI.UniversalTensorSquare.sg23031`, `OAI.UniversalTensorSquare.sg23032`, `OAI.UniversalTensorSquare.sg23038`, `OAI.UniversalTensorSquare.sg23057`, `OAI.UniversalTensorSquare.sg23075`, `OAI.UniversalTensorSquare.sg23082`, `OAI.UniversalTensorSquare.sg23087`, `OAI.UniversalTensorSquare.sg23096`, `OAI.UniversalTensorSquare.sg23105`, `OAI.UniversalTensorSquare.sg23110`, `OAI.UniversalTensorSquare.sg23122`, `OAI.UniversalTensorSquare.sg23123`, `OAI.UniversalTensorSquare.sg23129`, `OAI.UniversalTensorSquare.sg23134`, `OAI.UniversalTensorSquare.sg23135`, `OAI.UniversalTensorSquare.sg23142`, `OAI.UniversalTensorSquare.sg23148`, `OAI.UniversalTensorSquare.sg23164`, `OAI.UniversalTensorSquare.sg23193`, `OAI.UniversalTensorSquare.sg23197`, `OAI.UniversalTensorSquare.sg23221`, `OAI.UniversalTensorSquare.sg23231`, `OAI.UniversalTensorSquare.sg23232`, `OAI.UniversalTensorSquare.sg23234`, `OAI.UniversalTensorSquare.sg23235`, `OAI.UniversalTensorSquare.sg23238`, `OAI.UniversalTensorSquare.sg23239`, `OAI.UniversalTensorSquare.sg23245`, `OAI.UniversalTensorSquare.sg23252`, `OAI.UniversalTensorSquare.sg23253`, `OAI.UniversalTensorSquare.sg23259`, `OAI.UniversalTensorSquare.sg23268`, `OAI.UniversalTensorSquare.sg23281`, `OAI.UniversalTensorSquare.sg23282`, `OAI.UniversalTensorSquare.sg23289`, `OAI.UniversalTensorSquare.sg23290`, `OAI.UniversalTensorSquare.sg23295`, `OAI.UniversalTensorSquare.sg23308`, `OAI.UniversalTensorSquare.sg23314`, `OAI.UniversalTensorSquare.sg23315`, `OAI.UniversalTensorSquare.sg23318`, `OAI.UniversalTensorSquare.sg23321`, `OAI.UniversalTensorSquare.sg23324`, `OAI.UniversalTensorSquare.sg23339`, `OAI.UniversalTensorSquare.sg23344`, `OAI.UniversalTensorSquare.sg2335`, `OAI.UniversalTensorSquare.sg23390`, `OAI.UniversalTensorSquare.sg23397`, `OAI.UniversalTensorSquare.sg23408`, `OAI.UniversalTensorSquare.sg23419`, `OAI.UniversalTensorSquare.sg23423`, `OAI.UniversalTensorSquare.sg23424`, `OAI.UniversalTensorSquare.sg23431`, `OAI.UniversalTensorSquare.sg23434`, `OAI.UniversalTensorSquare.sg23440`, `OAI.UniversalTensorSquare.sg23441`, `OAI.UniversalTensorSquare.sg23447`, `OAI.UniversalTensorSquare.sg23448`, `OAI.UniversalTensorSquare.sg23451`, `OAI.UniversalTensorSquare.sg23463`, `OAI.UniversalTensorSquare.sg23464`, `OAI.UniversalTensorSquare.sg23468`, `OAI.UniversalTensorSquare.sg23473`, `OAI.UniversalTensorSquare.sg23479`, `OAI.UniversalTensorSquare.sg23480`, `OAI.UniversalTensorSquare.sg23481`, `OAI.UniversalTensorSquare.sg23487`, `OAI.UniversalTensorSquare.sg23496`, `OAI.UniversalTensorSquare.sg23500`, `OAI.UniversalTensorSquare.sg23509`, `OAI.UniversalTensorSquare.sg23510`, `OAI.UniversalTensorSquare.sg23525`, `OAI.UniversalTensorSquare.sg23528`, `OAI.UniversalTensorSquare.sg23529`, `OAI.UniversalTensorSquare.sg23566`, `OAI.UniversalTensorSquare.sg23569`, `OAI.UniversalTensorSquare.sg23573`, `OAI.UniversalTensorSquare.sg23578`, `OAI.UniversalTensorSquare.sg23583`, `OAI.UniversalTensorSquare.sg23586`, `OAI.UniversalTensorSquare.sg23593`, `OAI.UniversalTensorSquare.sg23595`, `OAI.UniversalTensorSquare.sg23599`, `OAI.UniversalTensorSquare.sg23600`, `OAI.UniversalTensorSquare.sg23606`, `OAI.UniversalTensorSquare.sg23608`, `OAI.UniversalTensorSquare.sg23610`, `OAI.UniversalTensorSquare.sg23611`, `OAI.UniversalTensorSquare.sg23620`, `OAI.UniversalTensorSquare.sg23623`, `OAI.UniversalTensorSquare.sg23627`, `OAI.UniversalTensorSquare.sg23630`, `OAI.UniversalTensorSquare.sg23632`, `OAI.UniversalTensorSquare.sg23634`, `OAI.UniversalTensorSquare.sg23635`, `OAI.UniversalTensorSquare.sg23636`, `OAI.UniversalTensorSquare.sg23637`, `OAI.UniversalTensorSquare.sg23657`, `OAI.UniversalTensorSquare.sg23658`, `OAI.UniversalTensorSquare.sg23663`, `OAI.UniversalTensorSquare.sg23670`, `OAI.UniversalTensorSquare.sg23677`, `OAI.UniversalTensorSquare.sg23680`, `OAI.UniversalTensorSquare.sg23681`, `OAI.UniversalTensorSquare.sg23682`, `OAI.UniversalTensorSquare.sg23683`, `OAI.UniversalTensorSquare.sg23684`, `OAI.UniversalTensorSquare.sg23687`, `OAI.UniversalTensorSquare.sg23689`, `OAI.UniversalTensorSquare.sg23690`, `OAI.UniversalTensorSquare.sg23691`, `OAI.UniversalTensorSquare.sg23692`, `OAI.UniversalTensorSquare.sg23698`, `OAI.UniversalTensorSquare.sg23710`, `OAI.UniversalTensorSquare.sg23729`, `OAI.UniversalTensorSquare.sg23735`, `OAI.UniversalTensorSquare.sg23744`, `OAI.UniversalTensorSquare.sg23747`, `OAI.UniversalTensorSquare.sg23752`, `OAI.UniversalTensorSquare.sg23754`, `OAI.UniversalTensorSquare.sg23766`, `OAI.UniversalTensorSquare.sg23767`, `OAI.UniversalTensorSquare.sg23780`, `OAI.UniversalTensorSquare.sg23785`, `OAI.UniversalTensorSquare.sg23794`, `OAI.UniversalTensorSquare.sg23798`, `OAI.UniversalTensorSquare.sg23800`, `OAI.UniversalTensorSquare.sg23808`, `OAI.UniversalTensorSquare.sg23809`, `OAI.UniversalTensorSquare.sg23815`, `OAI.UniversalTensorSquare.sg23816`, `OAI.UniversalTensorSquare.sg23819`, `OAI.UniversalTensorSquare.sg23820`, `OAI.UniversalTensorSquare.sg23823`, `OAI.UniversalTensorSquare.sg23826`, `OAI.UniversalTensorSquare.sg23838`, `OAI.UniversalTensorSquare.sg23840`, `OAI.UniversalTensorSquare.sg23842`, `OAI.UniversalTensorSquare.sg23856`, `OAI.UniversalTensorSquare.sg23872`, `OAI.UniversalTensorSquare.sg23874`, `OAI.UniversalTensorSquare.sg23880`, `OAI.UniversalTensorSquare.sg23883`, `OAI.UniversalTensorSquare.sg23887`, `OAI.UniversalTensorSquare.sg23889`, `OAI.UniversalTensorSquare.sg23893`, `OAI.UniversalTensorSquare.sg23902`, `OAI.UniversalTensorSquare.sg23907`, `OAI.UniversalTensorSquare.sg23923`, `OAI.UniversalTensorSquare.sg23935`, `OAI.UniversalTensorSquare.sg23936`, `OAI.UniversalTensorSquare.sg23938`, `OAI.UniversalTensorSquare.sg23940`, `OAI.UniversalTensorSquare.sg23941`, `OAI.UniversalTensorSquare.sg23952`, `OAI.UniversalTensorSquare.sg23954`, `OAI.UniversalTensorSquare.sg23961`, `OAI.UniversalTensorSquare.sg23964`, `OAI.UniversalTensorSquare.sg23970`, `OAI.UniversalTensorSquare.sg23973`, `OAI.UniversalTensorSquare.sg23980`, `OAI.UniversalTensorSquare.sg23981`, `OAI.UniversalTensorSquare.sg23994`, `OAI.UniversalTensorSquare.sg23996`, `OAI.UniversalTensorSquare.sg24002`, `OAI.UniversalTensorSquare.sg24008`, `OAI.UniversalTensorSquare.sg24010`, `OAI.UniversalTensorSquare.sg24014`, `OAI.UniversalTensorSquare.sg24019`, `OAI.UniversalTensorSquare.sg24022`, `OAI.UniversalTensorSquare.sg24024`, `OAI.UniversalTensorSquare.sg24036`, `OAI.UniversalTensorSquare.sg24040`, `OAI.UniversalTensorSquare.sg24041`, `OAI.UniversalTensorSquare.sg24044`, `OAI.UniversalTensorSquare.sg24048`, `OAI.UniversalTensorSquare.sg24049`, `OAI.UniversalTensorSquare.sg24052`, `OAI.UniversalTensorSquare.sg24054`, `OAI.UniversalTensorSquare.sg24067`, `OAI.UniversalTensorSquare.sg24069`, `OAI.UniversalTensorSquare.sg24070`, `OAI.UniversalTensorSquare.sg24072`, `OAI.UniversalTensorSquare.sg24073`, `OAI.UniversalTensorSquare.sg24083`, `OAI.UniversalTensorSquare.sg24087`, `OAI.UniversalTensorSquare.sg24099`, `OAI.UniversalTensorSquare.sg24103`, `OAI.UniversalTensorSquare.sg24104`, `OAI.UniversalTensorSquare.sg24107`, `OAI.UniversalTensorSquare.sg24116`, `OAI.UniversalTensorSquare.sg24121`, `OAI.UniversalTensorSquare.sg24126`, `OAI.UniversalTensorSquare.sg24136`, `OAI.UniversalTensorSquare.sg24139`, `OAI.UniversalTensorSquare.sg24140`, `OAI.UniversalTensorSquare.sg24144`, `OAI.UniversalTensorSquare.sg24149`, `OAI.UniversalTensorSquare.sg24150`, `OAI.UniversalTensorSquare.sg24153`, `OAI.UniversalTensorSquare.sg24154`, `OAI.UniversalTensorSquare.sg24155`, `OAI.UniversalTensorSquare.sg24157`, `OAI.UniversalTensorSquare.sg24158`, `OAI.UniversalTensorSquare.sg24160`, `OAI.UniversalTensorSquare.sg24166`, `OAI.UniversalTensorSquare.sg24167`, `OAI.UniversalTensorSquare.sg24169`, `OAI.UniversalTensorSquare.sg24171`, `OAI.UniversalTensorSquare.sg24174`, `OAI.UniversalTensorSquare.sg24183`, `OAI.UniversalTensorSquare.sg24185`, `OAI.UniversalTensorSquare.sg24188`, `OAI.UniversalTensorSquare.sg24192`, `OAI.UniversalTensorSquare.sg24194`, `OAI.UniversalTensorSquare.sg24196`, `OAI.UniversalTensorSquare.sg24197`, `OAI.UniversalTensorSquare.sg24200`, `OAI.UniversalTensorSquare.sg24203`, `OAI.UniversalTensorSquare.sg24209`, `OAI.UniversalTensorSquare.sg24210`, `OAI.UniversalTensorSquare.sg24212`, `OAI.UniversalTensorSquare.sg24217`, `OAI.UniversalTensorSquare.sg24222`, `OAI.UniversalTensorSquare.sg24227`, `OAI.UniversalTensorSquare.sg24257`, `OAI.UniversalTensorSquare.sg24270`, `OAI.UniversalTensorSquare.sg24275`, `OAI.UniversalTensorSquare.sg24281`, `OAI.UniversalTensorSquare.sg24285`, `OAI.UniversalTensorSquare.sg24287`, `OAI.UniversalTensorSquare.sg24292`, `OAI.UniversalTensorSquare.sg24296`, `OAI.UniversalTensorSquare.sg24303`, `OAI.UniversalTensorSquare.sg24308`, `OAI.UniversalTensorSquare.sg24310`, `OAI.UniversalTensorSquare.sg24313`, `OAI.UniversalTensorSquare.sg24315`, `OAI.UniversalTensorSquare.sg24321`, `OAI.UniversalTensorSquare.sg24330`, `OAI.UniversalTensorSquare.sg24339`, `OAI.UniversalTensorSquare.sg24347`, `OAI.UniversalTensorSquare.sg24354`, `OAI.UniversalTensorSquare.sg24355`, `OAI.UniversalTensorSquare.sg24356`, `OAI.UniversalTensorSquare.sg24361`, `OAI.UniversalTensorSquare.sg24367`, `OAI.UniversalTensorSquare.sg24371`, `OAI.UniversalTensorSquare.sg24376`, `OAI.UniversalTensorSquare.sg24378`, `OAI.UniversalTensorSquare.sg24379`, `OAI.UniversalTensorSquare.sg24380`, `OAI.UniversalTensorSquare.sg24385`, `OAI.UniversalTensorSquare.sg24389`, `OAI.UniversalTensorSquare.sg24408`, `OAI.UniversalTensorSquare.sg24415`, `OAI.UniversalTensorSquare.sg24417`, `OAI.UniversalTensorSquare.sg24423`, `OAI.UniversalTensorSquare.sg24424`, `OAI.UniversalTensorSquare.sg24425`, `OAI.UniversalTensorSquare.sg24432`, `OAI.UniversalTensorSquare.sg24438`, `OAI.UniversalTensorSquare.sg24439`, `OAI.UniversalTensorSquare.sg24446`, `OAI.UniversalTensorSquare.sg24448`, `OAI.UniversalTensorSquare.sg24450`, `OAI.UniversalTensorSquare.sg24451`, `OAI.UniversalTensorSquare.sg24452`, `OAI.UniversalTensorSquare.sg24453`, `OAI.UniversalTensorSquare.sg24464`, `OAI.UniversalTensorSquare.sg24467`, `OAI.UniversalTensorSquare.sg24469`, `OAI.UniversalTensorSquare.sg24470`, `OAI.UniversalTensorSquare.sg24471`, `OAI.UniversalTensorSquare.sg24479`, `OAI.UniversalTensorSquare.sg24481`, `OAI.UniversalTensorSquare.sg24483`, `OAI.UniversalTensorSquare.sg24495`, `OAI.UniversalTensorSquare.sg24497`, `OAI.UniversalTensorSquare.sg24502`, `OAI.UniversalTensorSquare.sg24504`, `OAI.UniversalTensorSquare.sg24505`, `OAI.UniversalTensorSquare.sg24506`, `OAI.UniversalTensorSquare.sg24508`, `OAI.UniversalTensorSquare.sg24509`, `OAI.UniversalTensorSquare.sg24516`, `OAI.UniversalTensorSquare.sg24518`, `OAI.UniversalTensorSquare.sg24522`, `OAI.UniversalTensorSquare.sg24526`, `OAI.UniversalTensorSquare.sg24529`, `OAI.UniversalTensorSquare.sg24532`, `OAI.UniversalTensorSquare.sg24535`, `OAI.UniversalTensorSquare.sg24537`, `OAI.UniversalTensorSquare.sg24539`, `OAI.UniversalTensorSquare.sg24540`, `OAI.UniversalTensorSquare.sg24541`, `OAI.UniversalTensorSquare.sg24545`, `OAI.UniversalTensorSquare.sg24547`, `OAI.UniversalTensorSquare.sg24551`, `OAI.UniversalTensorSquare.sg24552`, `OAI.UniversalTensorSquare.sg24557`, `OAI.UniversalTensorSquare.sg24558`, `OAI.UniversalTensorSquare.sg24559`, `OAI.UniversalTensorSquare.sg24560`, `OAI.UniversalTensorSquare.sg24562`, `OAI.UniversalTensorSquare.sg24564`, `OAI.UniversalTensorSquare.sg24566`, `OAI.UniversalTensorSquare.sg24567`, `OAI.UniversalTensorSquare.sg24568`, `OAI.UniversalTensorSquare.sg24571`, `OAI.UniversalTensorSquare.sg24573`, `OAI.UniversalTensorSquare.sg24576`, `OAI.UniversalTensorSquare.sg24577`, `OAI.UniversalTensorSquare.sg24579`, `OAI.UniversalTensorSquare.sg24586`, `OAI.UniversalTensorSquare.sg24587`, `OAI.UniversalTensorSquare.sg24592`, `OAI.UniversalTensorSquare.sg24596`, `OAI.UniversalTensorSquare.sg24599`, `OAI.UniversalTensorSquare.sg24602`, `OAI.UniversalTensorSquare.sg24609`, `OAI.UniversalTensorSquare.sg24612`, `OAI.UniversalTensorSquare.sg24614`, `OAI.UniversalTensorSquare.sg24622`, `OAI.UniversalTensorSquare.sg24623`, `OAI.UniversalTensorSquare.sg24627`, `OAI.UniversalTensorSquare.sg24628`, `OAI.UniversalTensorSquare.sg24630`, `OAI.UniversalTensorSquare.sg24633`, `OAI.UniversalTensorSquare.sg24635`, `OAI.UniversalTensorSquare.sg24636`, `OAI.UniversalTensorSquare.sg24637`, `OAI.UniversalTensorSquare.sg24638`, `OAI.UniversalTensorSquare.sg24639`, `OAI.UniversalTensorSquare.sg24644`, `OAI.UniversalTensorSquare.sg24646`, `OAI.UniversalTensorSquare.sg24648`, `OAI.UniversalTensorSquare.sg24649`, `OAI.UniversalTensorSquare.sg24650`, `OAI.UniversalTensorSquare.sg24652`, `OAI.UniversalTensorSquare.sg24653`, `OAI.UniversalTensorSquare.sg24654`, `OAI.UniversalTensorSquare.sg24655`, `OAI.UniversalTensorSquare.sg24656`, `OAI.UniversalTensorSquare.sg24657`, `OAI.UniversalTensorSquare.sg24658`, `OAI.UniversalTensorSquare.sg24659`, `OAI.UniversalTensorSquare.sg24660`, `OAI.UniversalTensorSquare.sg24662`, `OAI.UniversalTensorSquare.sg24663`, `OAI.UniversalTensorSquare.sg24664`, `OAI.UniversalTensorSquare.sg24665`, `OAI.UniversalTensorSquare.sg24666`, `OAI.UniversalTensorSquare.sg24668`, `OAI.UniversalTensorSquare.sg24669`, `OAI.UniversalTensorSquare.sg24670`, `OAI.UniversalTensorSquare.sg24671`, `OAI.UniversalTensorSquare.sg24672`, `OAI.UniversalTensorSquare.sg24674`, `OAI.UniversalTensorSquare.sg24676`, `OAI.UniversalTensorSquare.sg24680`, `OAI.UniversalTensorSquare.sg24681`, `OAI.UniversalTensorSquare.sg24682`, `OAI.UniversalTensorSquare.sg24684`, `OAI.UniversalTensorSquare.sg24685`, `OAI.UniversalTensorSquare.sg24686`, `OAI.UniversalTensorSquare.sg24688`, `OAI.UniversalTensorSquare.sg24691`, `OAI.UniversalTensorSquare.sg24692`, `OAI.UniversalTensorSquare.sg24693`, `OAI.UniversalTensorSquare.sg24695`, `OAI.UniversalTensorSquare.sg24697`, `OAI.UniversalTensorSquare.sg24700`, `OAI.UniversalTensorSquare.sg24701`, `OAI.UniversalTensorSquare.sg24706`, `OAI.UniversalTensorSquare.sg24708`, `OAI.UniversalTensorSquare.sg24709`, `OAI.UniversalTensorSquare.sg24710`, `OAI.UniversalTensorSquare.sg24712`, `OAI.UniversalTensorSquare.sg24713`, `OAI.UniversalTensorSquare.sg24715`, `OAI.UniversalTensorSquare.sg24716`, `OAI.UniversalTensorSquare.sg24719`, `OAI.UniversalTensorSquare.sg24720`, `OAI.UniversalTensorSquare.sg24730`, `OAI.UniversalTensorSquare.sg24731`, `OAI.UniversalTensorSquare.sg24732`, `OAI.UniversalTensorSquare.sg24733`, `OAI.UniversalTensorSquare.sg24734`, `OAI.UniversalTensorSquare.sg24735`, `OAI.UniversalTensorSquare.sg24738`, `OAI.UniversalTensorSquare.sg24739`, `OAI.UniversalTensorSquare.sg24743`, `OAI.UniversalTensorSquare.sg24744`, `OAI.UniversalTensorSquare.sg24745`, `OAI.UniversalTensorSquare.sg24747`, `OAI.UniversalTensorSquare.sg24748`, `OAI.UniversalTensorSquare.sg24775`, `OAI.UniversalTensorSquare.sg24783`, `OAI.UniversalTensorSquare.sg24789`, `OAI.UniversalTensorSquare.sg24809`, `OAI.UniversalTensorSquare.sg24811`, `OAI.UniversalTensorSquare.sg24816`, `OAI.UniversalTensorSquare.sg24817`, `OAI.UniversalTensorSquare.sg24818`, `OAI.UniversalTensorSquare.sg24820`, `OAI.UniversalTensorSquare.sg24821`, `OAI.UniversalTensorSquare.sg24825`, `OAI.UniversalTensorSquare.sg24826`, `OAI.UniversalTensorSquare.sg24827`, `OAI.UniversalTensorSquare.sg24832`, `OAI.UniversalTensorSquare.sg24840`, `OAI.UniversalTensorSquare.sg24843`, `OAI.UniversalTensorSquare.sg24845`, `OAI.UniversalTensorSquare.sg24846`, `OAI.UniversalTensorSquare.sg24851`, `OAI.UniversalTensorSquare.sg24861`, `OAI.UniversalTensorSquare.sg24865`, `OAI.UniversalTensorSquare.sg24876`, `OAI.UniversalTensorSquare.sg24879`, `OAI.UniversalTensorSquare.sg24882`, `OAI.UniversalTensorSquare.sg24885`, `OAI.UniversalTensorSquare.sg24886`, `OAI.UniversalTensorSquare.sg24887`, `OAI.UniversalTensorSquare.sg24889`, `OAI.UniversalTensorSquare.sg24893`, `OAI.UniversalTensorSquare.sg24896`, `OAI.UniversalTensorSquare.sg24897`, `OAI.UniversalTensorSquare.sg24898`, `OAI.UniversalTensorSquare.sg24899`, `OAI.UniversalTensorSquare.sg24911`, `OAI.UniversalTensorSquare.sg24913`, `OAI.UniversalTensorSquare.sg24917`, `OAI.UniversalTensorSquare.sg24919`, `OAI.UniversalTensorSquare.sg24920`, `OAI.UniversalTensorSquare.sg24923`, `OAI.UniversalTensorSquare.sg24928`, `OAI.UniversalTensorSquare.sg24931`, `OAI.UniversalTensorSquare.sg24939`, `OAI.UniversalTensorSquare.sg24941`, `OAI.UniversalTensorSquare.sg24942`, `OAI.UniversalTensorSquare.sg24943`, `OAI.UniversalTensorSquare.sg24944`, `OAI.UniversalTensorSquare.sg24949`, `OAI.UniversalTensorSquare.sg24952`, `OAI.UniversalTensorSquare.sg24953`, `OAI.UniversalTensorSquare.sg24954`, `OAI.UniversalTensorSquare.sg24955`, `OAI.UniversalTensorSquare.sg24956`, `OAI.UniversalTensorSquare.sg24958`, `OAI.UniversalTensorSquare.sg24959`, `OAI.UniversalTensorSquare.sg24960`, `OAI.UniversalTensorSquare.sg24964`, `OAI.UniversalTensorSquare.sg24967`, `OAI.UniversalTensorSquare.sg24971`, `OAI.UniversalTensorSquare.sg24972`, `OAI.UniversalTensorSquare.sg24975`, `OAI.UniversalTensorSquare.sg24984`, `OAI.UniversalTensorSquare.sg24987`, `OAI.UniversalTensorSquare.sg24989`, `OAI.UniversalTensorSquare.sg24990`, `OAI.UniversalTensorSquare.sg24991`, `OAI.UniversalTensorSquare.sg24996`, `OAI.UniversalTensorSquare.sg24997`, `OAI.UniversalTensorSquare.sg24998`, `OAI.UniversalTensorSquare.sg25000`, `OAI.UniversalTensorSquare.sg25003`, `OAI.UniversalTensorSquare.sg25005`, `OAI.UniversalTensorSquare.sg25007`, `OAI.UniversalTensorSquare.sg25008`, `OAI.UniversalTensorSquare.sg25009`, `OAI.UniversalTensorSquare.sg25011`, `OAI.UniversalTensorSquare.sg25013`, `OAI.UniversalTensorSquare.sg25015`, `OAI.UniversalTensorSquare.sg25016`, `OAI.UniversalTensorSquare.sg25018`, `OAI.UniversalTensorSquare.sg25019`, `OAI.UniversalTensorSquare.sg25020`, `OAI.UniversalTensorSquare.sg25021`, `OAI.UniversalTensorSquare.sg25022`, `OAI.UniversalTensorSquare.sg25024`, `OAI.UniversalTensorSquare.sg25025`, `OAI.UniversalTensorSquare.sg25026`, `OAI.UniversalTensorSquare.sg25028`, `OAI.UniversalTensorSquare.sg25030`, `OAI.UniversalTensorSquare.sg25032`, `OAI.UniversalTensorSquare.sg25034`, `OAI.UniversalTensorSquare.sg25036`, `OAI.UniversalTensorSquare.sg25039`, `OAI.UniversalTensorSquare.sg25040`, `OAI.UniversalTensorSquare.sg25041`, `OAI.UniversalTensorSquare.sg25042`, `OAI.UniversalTensorSquare.sg25044`, `OAI.UniversalTensorSquare.sg25045`, `OAI.UniversalTensorSquare.sg25046`, `OAI.UniversalTensorSquare.sg25048`, `OAI.UniversalTensorSquare.sg25050`, `OAI.UniversalTensorSquare.sg25051`, `OAI.UniversalTensorSquare.sg25053`, `OAI.UniversalTensorSquare.sg25056`, `OAI.UniversalTensorSquare.sg25057`, `OAI.UniversalTensorSquare.sg25058`, `OAI.UniversalTensorSquare.sg25062`, `OAI.UniversalTensorSquare.sg25064`, `OAI.UniversalTensorSquare.sg25066`, `OAI.UniversalTensorSquare.sg25068`, `OAI.UniversalTensorSquare.sg25069`, `OAI.UniversalTensorSquare.sg25070`, `OAI.UniversalTensorSquare.sg25074`, `OAI.UniversalTensorSquare.sg25075`, `OAI.UniversalTensorSquare.sg25076`, `OAI.UniversalTensorSquare.sg25082`, `OAI.UniversalTensorSquare.sg25101`, `OAI.UniversalTensorSquare.sg25111`, `OAI.UniversalTensorSquare.sg25123`, `OAI.UniversalTensorSquare.sg25124`, `OAI.UniversalTensorSquare.sg25135`, `OAI.UniversalTensorSquare.sg25138`, `OAI.UniversalTensorSquare.sg25148`, `OAI.UniversalTensorSquare.sg25154`, `OAI.UniversalTensorSquare.sg25163`, `OAI.UniversalTensorSquare.sg25168`, `OAI.UniversalTensorSquare.sg25175`, `OAI.UniversalTensorSquare.sg25177`, `OAI.UniversalTensorSquare.sg25182`, `OAI.UniversalTensorSquare.sg25184`, `OAI.UniversalTensorSquare.sg25185`, `OAI.UniversalTensorSquare.sg25187`, `OAI.UniversalTensorSquare.sg25189`, `OAI.UniversalTensorSquare.sg25194`, `OAI.UniversalTensorSquare.sg25196`, `OAI.UniversalTensorSquare.sg25200`, `OAI.UniversalTensorSquare.sg25207`, `OAI.UniversalTensorSquare.sg25209`, `OAI.UniversalTensorSquare.sg25215`, `OAI.UniversalTensorSquare.sg25217`, `OAI.UniversalTensorSquare.sg25223`, `OAI.UniversalTensorSquare.sg25227`, `OAI.UniversalTensorSquare.sg25230`, `OAI.UniversalTensorSquare.sg25238`, `OAI.UniversalTensorSquare.sg25239`, `OAI.UniversalTensorSquare.sg25247`, `OAI.UniversalTensorSquare.sg25249`, `OAI.UniversalTensorSquare.sg25262`, `OAI.UniversalTensorSquare.sg25264`, `OAI.UniversalTensorSquare.sg25267`, `OAI.UniversalTensorSquare.sg25270`, `OAI.UniversalTensorSquare.sg25271`, `OAI.UniversalTensorSquare.sg25275`, `OAI.UniversalTensorSquare.sg25277`, `OAI.UniversalTensorSquare.sg25278`, `OAI.UniversalTensorSquare.sg25279`, `OAI.UniversalTensorSquare.sg25284`, `OAI.UniversalTensorSquare.sg25285`, `OAI.UniversalTensorSquare.sg25286`, `OAI.UniversalTensorSquare.sg25290`, `OAI.UniversalTensorSquare.sg25292`, `OAI.UniversalTensorSquare.sg25293`, `OAI.UniversalTensorSquare.sg25294`, `OAI.UniversalTensorSquare.sg25298`, `OAI.UniversalTensorSquare.sg25303`, `OAI.UniversalTensorSquare.sg25307`, `OAI.UniversalTensorSquare.sg25310`, `OAI.UniversalTensorSquare.sg25316`, `OAI.UniversalTensorSquare.sg25317`, `OAI.UniversalTensorSquare.sg25318`, `OAI.UniversalTensorSquare.sg25323`, `OAI.UniversalTensorSquare.sg25324`, `OAI.UniversalTensorSquare.sg25329`, `OAI.UniversalTensorSquare.sg25330`, `OAI.UniversalTensorSquare.sg25331`, `OAI.UniversalTensorSquare.sg25332`, `OAI.UniversalTensorSquare.sg25335`, `OAI.UniversalTensorSquare.sg25339`, `OAI.UniversalTensorSquare.sg25340`, `OAI.UniversalTensorSquare.sg25342`, `OAI.UniversalTensorSquare.sg25345`, `OAI.UniversalTensorSquare.sg25347`, `OAI.UniversalTensorSquare.sg25348`, `OAI.UniversalTensorSquare.sg25350`, `OAI.UniversalTensorSquare.sg25351`, `OAI.UniversalTensorSquare.sg25352`, `OAI.UniversalTensorSquare.sg25354`, `OAI.UniversalTensorSquare.sg25357`, `OAI.UniversalTensorSquare.sg25359`, `OAI.UniversalTensorSquare.sg25361`, `OAI.UniversalTensorSquare.sg25375`, `OAI.UniversalTensorSquare.sg25381`, `OAI.UniversalTensorSquare.sg25395`, `OAI.UniversalTensorSquare.sg25405`, `OAI.UniversalTensorSquare.sg25413`, `OAI.UniversalTensorSquare.sg25416`, `OAI.UniversalTensorSquare.sg25417`, `OAI.UniversalTensorSquare.sg25420`, `OAI.UniversalTensorSquare.sg25425`, `OAI.UniversalTensorSquare.sg25428`, `OAI.UniversalTensorSquare.sg25434`, `OAI.UniversalTensorSquare.sg25448`, `OAI.UniversalTensorSquare.sg25456`, `OAI.UniversalTensorSquare.sg25457`, `OAI.UniversalTensorSquare.sg25468`, `OAI.UniversalTensorSquare.sg25471`, `OAI.UniversalTensorSquare.sg25472`, `OAI.UniversalTensorSquare.sg25476`, `OAI.UniversalTensorSquare.sg25478`, `OAI.UniversalTensorSquare.sg25486`, `OAI.UniversalTensorSquare.sg25487`, `OAI.UniversalTensorSquare.sg25489`, `OAI.UniversalTensorSquare.sg25498`, `OAI.UniversalTensorSquare.sg25502`, `OAI.UniversalTensorSquare.sg25503`, `OAI.UniversalTensorSquare.sg25504`, `OAI.UniversalTensorSquare.sg25506`, `OAI.UniversalTensorSquare.sg25508`, `OAI.UniversalTensorSquare.sg25511`, `OAI.UniversalTensorSquare.sg25518`, `OAI.UniversalTensorSquare.sg25522`, `OAI.UniversalTensorSquare.sg25535`, `OAI.UniversalTensorSquare.sg25551`, `OAI.UniversalTensorSquare.sg25555`, `OAI.UniversalTensorSquare.sg25557`, `OAI.UniversalTensorSquare.sg25560`, `OAI.UniversalTensorSquare.sg25567`, `OAI.UniversalTensorSquare.sg25569`, `OAI.UniversalTensorSquare.sg25572`, `OAI.UniversalTensorSquare.sg25574`, `OAI.UniversalTensorSquare.sg25587`, `OAI.UniversalTensorSquare.sg25589`, `OAI.UniversalTensorSquare.sg25603`, `OAI.UniversalTensorSquare.sg25605`, `OAI.UniversalTensorSquare.sg25607`, `OAI.UniversalTensorSquare.sg25614`, `OAI.UniversalTensorSquare.sg25618`, `OAI.UniversalTensorSquare.sg25620`, `OAI.UniversalTensorSquare.sg25630`, `OAI.UniversalTensorSquare.sg25638`, `OAI.UniversalTensorSquare.sg25639`, `OAI.UniversalTensorSquare.sg25640`, `OAI.UniversalTensorSquare.sg25643`, `OAI.UniversalTensorSquare.sg25645`, `OAI.UniversalTensorSquare.sg25646`, `OAI.UniversalTensorSquare.sg25653`, `OAI.UniversalTensorSquare.sg25654`, `OAI.UniversalTensorSquare.sg25664`, `OAI.UniversalTensorSquare.sg25674`, `OAI.UniversalTensorSquare.sg25675`, `OAI.UniversalTensorSquare.sg25682`, `OAI.UniversalTensorSquare.sg25690`, `OAI.UniversalTensorSquare.sg25691`, `OAI.UniversalTensorSquare.sg25693`, `OAI.UniversalTensorSquare.sg25694`, `OAI.UniversalTensorSquare.sg25695`, `OAI.UniversalTensorSquare.sg25697`, `OAI.UniversalTensorSquare.sg25706`, `OAI.UniversalTensorSquare.sg25707`, `OAI.UniversalTensorSquare.sg25710`, `OAI.UniversalTensorSquare.sg25711`, `OAI.UniversalTensorSquare.sg25712`, `OAI.UniversalTensorSquare.sg25714`, `OAI.UniversalTensorSquare.sg25715`, `OAI.UniversalTensorSquare.sg25716`, `OAI.UniversalTensorSquare.sg25722`, `OAI.UniversalTensorSquare.sg25723`, `OAI.UniversalTensorSquare.sg25724`, `OAI.UniversalTensorSquare.sg25728`, `OAI.UniversalTensorSquare.sg25729`, `OAI.UniversalTensorSquare.sg25730`, `OAI.UniversalTensorSquare.sg25733`, `OAI.UniversalTensorSquare.sg25735`, `OAI.UniversalTensorSquare.sg25736`, `OAI.UniversalTensorSquare.sg25741`, `OAI.UniversalTensorSquare.sg25743`, `OAI.UniversalTensorSquare.sg25759`, `OAI.UniversalTensorSquare.sg25760`, `OAI.UniversalTensorSquare.sg25764`, `OAI.UniversalTensorSquare.sg25771`, `OAI.UniversalTensorSquare.sg25776`, `OAI.UniversalTensorSquare.sg25777`, `OAI.UniversalTensorSquare.sg25781`, `OAI.UniversalTensorSquare.sg25782`, `OAI.UniversalTensorSquare.sg25792`, `OAI.UniversalTensorSquare.sg25793`, `OAI.UniversalTensorSquare.sg25797`, `OAI.UniversalTensorSquare.sg25800`, `OAI.UniversalTensorSquare.sg25803`, `OAI.UniversalTensorSquare.sg25805`, `OAI.UniversalTensorSquare.sg25813`, `OAI.UniversalTensorSquare.sg25817`, `OAI.UniversalTensorSquare.sg25820`, `OAI.UniversalTensorSquare.sg25821`, `OAI.UniversalTensorSquare.sg25824`, `OAI.UniversalTensorSquare.sg25826`, `OAI.UniversalTensorSquare.sg25829`, `OAI.UniversalTensorSquare.sg2583`, `OAI.UniversalTensorSquare.sg25835`, `OAI.UniversalTensorSquare.sg25839`, `OAI.UniversalTensorSquare.sg25840`, `OAI.UniversalTensorSquare.sg25842`, `OAI.UniversalTensorSquare.sg25848`, `OAI.UniversalTensorSquare.sg2585`, `OAI.UniversalTensorSquare.sg25850`, `OAI.UniversalTensorSquare.sg25852`, `OAI.UniversalTensorSquare.sg25855`, `OAI.UniversalTensorSquare.sg25856`, `OAI.UniversalTensorSquare.sg25857`, `OAI.UniversalTensorSquare.sg25858`, `OAI.UniversalTensorSquare.sg25859`, `OAI.UniversalTensorSquare.sg25864`, `OAI.UniversalTensorSquare.sg25871`, `OAI.UniversalTensorSquare.sg25872`, `OAI.UniversalTensorSquare.sg25874`, `OAI.UniversalTensorSquare.sg25875`, `OAI.UniversalTensorSquare.sg25880`, `OAI.UniversalTensorSquare.sg25882`, `OAI.UniversalTensorSquare.sg25885`, `OAI.UniversalTensorSquare.sg25891`, `OAI.UniversalTensorSquare.sg25892`, `OAI.UniversalTensorSquare.sg25896`, `OAI.UniversalTensorSquare.sg25898`, `OAI.UniversalTensorSquare.sg25900`, `OAI.UniversalTensorSquare.sg25902`, `OAI.UniversalTensorSquare.sg25911`, `OAI.UniversalTensorSquare.sg25940`, `OAI.UniversalTensorSquare.sg25941`, `OAI.UniversalTensorSquare.sg25945`, `OAI.UniversalTensorSquare.sg25961`, `OAI.UniversalTensorSquare.sg25963`, `OAI.UniversalTensorSquare.sg25966`, `OAI.UniversalTensorSquare.sg25974`, `OAI.UniversalTensorSquare.sg25979`, `OAI.UniversalTensorSquare.sg25981`, `OAI.UniversalTensorSquare.sg25982`, `OAI.UniversalTensorSquare.sg25983`, `OAI.UniversalTensorSquare.sg25987`, `OAI.UniversalTensorSquare.sg25988`, `OAI.UniversalTensorSquare.sg26003`, `OAI.UniversalTensorSquare.sg26004`, `OAI.UniversalTensorSquare.sg26022`, `OAI.UniversalTensorSquare.sg26030`, `OAI.UniversalTensorSquare.sg26040`, `OAI.UniversalTensorSquare.sg26041`, `OAI.UniversalTensorSquare.sg26044`, `OAI.UniversalTensorSquare.sg26046`, `OAI.UniversalTensorSquare.sg26051`, `OAI.UniversalTensorSquare.sg26053`, `OAI.UniversalTensorSquare.sg26057`, `OAI.UniversalTensorSquare.sg26066`, `OAI.UniversalTensorSquare.sg26067`, `OAI.UniversalTensorSquare.sg26073`, `OAI.UniversalTensorSquare.sg26080`, `OAI.UniversalTensorSquare.sg26084`, `OAI.UniversalTensorSquare.sg26086`, `OAI.UniversalTensorSquare.sg26094`, `OAI.UniversalTensorSquare.sg26110`, `OAI.UniversalTensorSquare.sg26112`, `OAI.UniversalTensorSquare.sg26116`, `OAI.UniversalTensorSquare.sg26122`, `OAI.UniversalTensorSquare.sg26124`, `OAI.UniversalTensorSquare.sg26129`, `OAI.UniversalTensorSquare.sg26136`, `OAI.UniversalTensorSquare.sg26138`, `OAI.UniversalTensorSquare.sg26140`, `OAI.UniversalTensorSquare.sg26141`, `OAI.UniversalTensorSquare.sg26153`, `OAI.UniversalTensorSquare.sg26158`, `OAI.UniversalTensorSquare.sg26163`, `OAI.UniversalTensorSquare.sg26165`, `OAI.UniversalTensorSquare.sg26169`, `OAI.UniversalTensorSquare.sg26175`, `OAI.UniversalTensorSquare.sg26177`, `OAI.UniversalTensorSquare.sg26182`, `OAI.UniversalTensorSquare.sg26184`, `OAI.UniversalTensorSquare.sg26186`, `OAI.UniversalTensorSquare.sg26187`, `OAI.UniversalTensorSquare.sg26189`, `OAI.UniversalTensorSquare.sg26194`, `OAI.UniversalTensorSquare.sg26196`, `OAI.UniversalTensorSquare.sg26197`, `OAI.UniversalTensorSquare.sg26199`, `OAI.UniversalTensorSquare.sg26204`, `OAI.UniversalTensorSquare.sg26205`, `OAI.UniversalTensorSquare.sg26206`, `OAI.UniversalTensorSquare.sg26207`, `OAI.UniversalTensorSquare.sg26210`, `OAI.UniversalTensorSquare.sg26211`, `OAI.UniversalTensorSquare.sg26215`, `OAI.UniversalTensorSquare.sg26217`, `OAI.UniversalTensorSquare.sg26229`, `OAI.UniversalTensorSquare.sg26234`, `OAI.UniversalTensorSquare.sg26240`, `OAI.UniversalTensorSquare.sg26244`, `OAI.UniversalTensorSquare.sg26248`, `OAI.UniversalTensorSquare.sg26249`, `OAI.UniversalTensorSquare.sg26252`, `OAI.UniversalTensorSquare.sg26260`, `OAI.UniversalTensorSquare.sg26265`, `OAI.UniversalTensorSquare.sg26266`, `OAI.UniversalTensorSquare.sg26270`, `OAI.UniversalTensorSquare.sg26271`, `OAI.UniversalTensorSquare.sg26273`, `OAI.UniversalTensorSquare.sg26276`, `OAI.UniversalTensorSquare.sg26282`, `OAI.UniversalTensorSquare.sg26284`, `OAI.UniversalTensorSquare.sg26286`, `OAI.UniversalTensorSquare.sg26289`, `OAI.UniversalTensorSquare.sg26291`, `OAI.UniversalTensorSquare.sg26292`, `OAI.UniversalTensorSquare.sg26293`, `OAI.UniversalTensorSquare.sg26320`, `OAI.UniversalTensorSquare.sg26321`, `OAI.UniversalTensorSquare.sg26322`, `OAI.UniversalTensorSquare.sg26323`, `OAI.UniversalTensorSquare.sg26324`, `OAI.UniversalTensorSquare.sg26326`, `OAI.UniversalTensorSquare.sg26328`, `OAI.UniversalTensorSquare.sg26329`, `OAI.UniversalTensorSquare.sg26332`, `OAI.UniversalTensorSquare.sg26334`, `OAI.UniversalTensorSquare.sg26342`, `OAI.UniversalTensorSquare.sg26345`, `OAI.UniversalTensorSquare.sg26347`, `OAI.UniversalTensorSquare.sg26350`, `OAI.UniversalTensorSquare.sg26351`, `OAI.UniversalTensorSquare.sg26355`, `OAI.UniversalTensorSquare.sg26359`, `OAI.UniversalTensorSquare.sg26363`, `OAI.UniversalTensorSquare.sg26365`, `OAI.UniversalTensorSquare.sg26374`, `OAI.UniversalTensorSquare.sg26380`, `OAI.UniversalTensorSquare.sg26381`, `OAI.UniversalTensorSquare.sg26388`, `OAI.UniversalTensorSquare.sg26389`, `OAI.UniversalTensorSquare.sg26397`, `OAI.UniversalTensorSquare.sg26398`, `OAI.UniversalTensorSquare.sg26409`, `OAI.UniversalTensorSquare.sg26412`, `OAI.UniversalTensorSquare.sg26415`, `OAI.UniversalTensorSquare.sg26416`, `OAI.UniversalTensorSquare.sg26422`, `OAI.UniversalTensorSquare.sg26423`, `OAI.UniversalTensorSquare.sg26430`, `OAI.UniversalTensorSquare.sg26433`, `OAI.UniversalTensorSquare.sg26435`, `OAI.UniversalTensorSquare.sg26443`, `OAI.UniversalTensorSquare.sg26444`, `OAI.UniversalTensorSquare.sg26445`, `OAI.UniversalTensorSquare.sg26450`, `OAI.UniversalTensorSquare.sg26466`, `OAI.UniversalTensorSquare.sg26467`, `OAI.UniversalTensorSquare.sg26477`, `OAI.UniversalTensorSquare.sg26484`, `OAI.UniversalTensorSquare.sg26485`, `OAI.UniversalTensorSquare.sg26486`, `OAI.UniversalTensorSquare.sg26490`, `OAI.UniversalTensorSquare.sg26491`, `OAI.UniversalTensorSquare.sg26492`, `OAI.UniversalTensorSquare.sg26494`, `OAI.UniversalTensorSquare.sg26496`, `OAI.UniversalTensorSquare.sg26500`, `OAI.UniversalTensorSquare.sg26502`, `OAI.UniversalTensorSquare.sg26504`, `OAI.UniversalTensorSquare.sg26506`, `OAI.UniversalTensorSquare.sg26511`, `OAI.UniversalTensorSquare.sg26513`, `OAI.UniversalTensorSquare.sg26514`, `OAI.UniversalTensorSquare.sg26517`, `OAI.UniversalTensorSquare.sg26520`, `OAI.UniversalTensorSquare.sg26521`, `OAI.UniversalTensorSquare.sg26522`, `OAI.UniversalTensorSquare.sg26529`, `OAI.UniversalTensorSquare.sg26531`, `OAI.UniversalTensorSquare.sg26533`, `OAI.UniversalTensorSquare.sg26541`, `OAI.UniversalTensorSquare.sg26543`, `OAI.UniversalTensorSquare.sg26544`, `OAI.UniversalTensorSquare.sg26570`, `OAI.UniversalTensorSquare.sg26576`, `OAI.UniversalTensorSquare.sg26592`, `OAI.UniversalTensorSquare.sg26594`, `OAI.UniversalTensorSquare.sg26598`, `OAI.UniversalTensorSquare.sg26599`, `OAI.UniversalTensorSquare.sg26604`, `OAI.UniversalTensorSquare.sg26613`, `OAI.UniversalTensorSquare.sg26614`, `OAI.UniversalTensorSquare.sg26616`, `OAI.UniversalTensorSquare.sg26617`, `OAI.UniversalTensorSquare.sg26628`, `OAI.UniversalTensorSquare.sg26633`, `OAI.UniversalTensorSquare.sg26634`, `OAI.UniversalTensorSquare.sg26644`, `OAI.UniversalTensorSquare.sg26645`, `OAI.UniversalTensorSquare.sg26650`, `OAI.UniversalTensorSquare.sg26651`, `OAI.UniversalTensorSquare.sg26662`, `OAI.UniversalTensorSquare.sg26666`, `OAI.UniversalTensorSquare.sg26671`, `OAI.UniversalTensorSquare.sg26674`, `OAI.UniversalTensorSquare.sg26686`, `OAI.UniversalTensorSquare.sg26689`, `OAI.UniversalTensorSquare.sg26697`, `OAI.UniversalTensorSquare.sg26698`, `OAI.UniversalTensorSquare.sg26702`, `OAI.UniversalTensorSquare.sg26707`, `OAI.UniversalTensorSquare.sg26712`, `OAI.UniversalTensorSquare.sg26715`, `OAI.UniversalTensorSquare.sg26724`, `OAI.UniversalTensorSquare.sg26726`, `OAI.UniversalTensorSquare.sg26731`, `OAI.UniversalTensorSquare.sg26738`, `OAI.UniversalTensorSquare.sg26742`, `OAI.UniversalTensorSquare.sg26745`, `OAI.UniversalTensorSquare.sg26746`, `OAI.UniversalTensorSquare.sg26747`, `OAI.UniversalTensorSquare.sg26752`, `OAI.UniversalTensorSquare.sg26757`, `OAI.UniversalTensorSquare.sg26758`, `OAI.UniversalTensorSquare.sg26759`, `OAI.UniversalTensorSquare.sg26763`, `OAI.UniversalTensorSquare.sg26764`, `OAI.UniversalTensorSquare.sg26765`, `OAI.UniversalTensorSquare.sg26769`, `OAI.UniversalTensorSquare.sg26801`, `OAI.UniversalTensorSquare.sg26811`, `OAI.UniversalTensorSquare.sg26823`, `OAI.UniversalTensorSquare.sg26824`, `OAI.UniversalTensorSquare.sg26849`, `OAI.UniversalTensorSquare.sg26859`, `OAI.UniversalTensorSquare.sg26860`, `OAI.UniversalTensorSquare.sg26865`, `OAI.UniversalTensorSquare.sg26873`, `OAI.UniversalTensorSquare.sg26877`, `OAI.UniversalTensorSquare.sg26881`, `OAI.UniversalTensorSquare.sg26884`, `OAI.UniversalTensorSquare.sg26892`, `OAI.UniversalTensorSquare.sg26898`, `OAI.UniversalTensorSquare.sg26899`, `OAI.UniversalTensorSquare.sg26900`, `OAI.UniversalTensorSquare.sg26927`, `OAI.UniversalTensorSquare.sg26930`, `OAI.UniversalTensorSquare.sg26942`, `OAI.UniversalTensorSquare.sg26944`, `OAI.UniversalTensorSquare.sg26946`, `OAI.UniversalTensorSquare.sg26947`, `OAI.UniversalTensorSquare.sg26949`, `OAI.UniversalTensorSquare.sg26950`, `OAI.UniversalTensorSquare.sg26954`, `OAI.UniversalTensorSquare.sg26955`, `OAI.UniversalTensorSquare.sg26956`, `OAI.UniversalTensorSquare.sg26957`, `OAI.UniversalTensorSquare.sg26958`, `OAI.UniversalTensorSquare.sg26959`, `OAI.UniversalTensorSquare.sg26960`, `OAI.UniversalTensorSquare.sg26963`, `OAI.UniversalTensorSquare.sg26972`, `OAI.UniversalTensorSquare.sg27002`, `OAI.UniversalTensorSquare.sg27004`, `OAI.UniversalTensorSquare.sg27005`, `OAI.UniversalTensorSquare.sg27007`, `OAI.UniversalTensorSquare.sg27009`, `OAI.UniversalTensorSquare.sg27011`, `OAI.UniversalTensorSquare.sg27013`, `OAI.UniversalTensorSquare.sg27014`, `OAI.UniversalTensorSquare.sg27015`, `OAI.UniversalTensorSquare.sg27019`, `OAI.UniversalTensorSquare.sg27057`, `OAI.UniversalTensorSquare.sg27059`, `OAI.UniversalTensorSquare.sg27063`, `OAI.UniversalTensorSquare.sg27066`, `OAI.UniversalTensorSquare.sg27072`, `OAI.UniversalTensorSquare.sg27074`, `OAI.UniversalTensorSquare.sg27075`, `OAI.UniversalTensorSquare.sg27078`, `OAI.UniversalTensorSquare.sg27079`, `OAI.UniversalTensorSquare.sg27083`, `OAI.UniversalTensorSquare.sg27085`, `OAI.UniversalTensorSquare.sg27087`, `OAI.UniversalTensorSquare.sg27089`, `OAI.UniversalTensorSquare.sg27091`, `OAI.UniversalTensorSquare.sg27092`, `OAI.UniversalTensorSquare.sg27093`, `OAI.UniversalTensorSquare.sg27095`, `OAI.UniversalTensorSquare.sg27096`, `OAI.UniversalTensorSquare.sg27097`, `OAI.UniversalTensorSquare.sg27107`, `OAI.UniversalTensorSquare.sg27108`, `OAI.UniversalTensorSquare.sg27109`, `OAI.UniversalTensorSquare.sg27111`, `OAI.UniversalTensorSquare.sg27112`, `OAI.UniversalTensorSquare.sg27115`, `OAI.UniversalTensorSquare.sg27119`, `OAI.UniversalTensorSquare.sg27121`, `OAI.UniversalTensorSquare.sg27122`, `OAI.UniversalTensorSquare.sg27124`, `OAI.UniversalTensorSquare.sg27125`, `OAI.UniversalTensorSquare.sg27127`, `OAI.UniversalTensorSquare.sg27129`, `OAI.UniversalTensorSquare.sg27130`, `OAI.UniversalTensorSquare.sg27131`, `OAI.UniversalTensorSquare.sg27161`, `OAI.UniversalTensorSquare.sg27165`, `OAI.UniversalTensorSquare.sg27173`, `OAI.UniversalTensorSquare.sg27175`, `OAI.UniversalTensorSquare.sg27186`, `OAI.UniversalTensorSquare.sg27188`, `OAI.UniversalTensorSquare.sg27190`, `OAI.UniversalTensorSquare.sg27197`, `OAI.UniversalTensorSquare.sg27198`, `OAI.UniversalTensorSquare.sg27200`, `OAI.UniversalTensorSquare.sg27202`, `OAI.UniversalTensorSquare.sg27204`, `OAI.UniversalTensorSquare.sg27206`, `OAI.UniversalTensorSquare.sg27208`, `OAI.UniversalTensorSquare.sg27209`, `OAI.UniversalTensorSquare.sg27213`, `OAI.UniversalTensorSquare.sg27217`, `OAI.UniversalTensorSquare.sg27219`, `OAI.UniversalTensorSquare.sg27220`, `OAI.UniversalTensorSquare.sg27222`, `OAI.UniversalTensorSquare.sg27227`, `OAI.UniversalTensorSquare.sg27228`, `OAI.UniversalTensorSquare.sg27231`, `OAI.UniversalTensorSquare.sg27233`, `OAI.UniversalTensorSquare.sg27236`, `OAI.UniversalTensorSquare.sg27237`, `OAI.UniversalTensorSquare.sg27247`, `OAI.UniversalTensorSquare.sg27249`, `OAI.UniversalTensorSquare.sg27251`, `OAI.UniversalTensorSquare.sg27253`, `OAI.UniversalTensorSquare.sg27254`, `OAI.UniversalTensorSquare.sg27255`, `OAI.UniversalTensorSquare.sg27258`, `OAI.UniversalTensorSquare.sg27259`, `OAI.UniversalTensorSquare.sg27260`, `OAI.UniversalTensorSquare.sg27262`, `OAI.UniversalTensorSquare.sg27263`, `OAI.UniversalTensorSquare.sg27264`, `OAI.UniversalTensorSquare.sg27265`, `OAI.UniversalTensorSquare.sg27266`, `OAI.UniversalTensorSquare.sg27267`, `OAI.UniversalTensorSquare.sg27268`, `OAI.UniversalTensorSquare.sg27269`, `OAI.UniversalTensorSquare.sg27272`, `OAI.UniversalTensorSquare.sg27273`, `OAI.UniversalTensorSquare.sg27275`, `OAI.UniversalTensorSquare.sg27277`, `OAI.UniversalTensorSquare.sg27279`, `OAI.UniversalTensorSquare.sg27280`, `OAI.UniversalTensorSquare.sg27281`, `OAI.UniversalTensorSquare.sg27282`, `OAI.UniversalTensorSquare.sg27283`, `OAI.UniversalTensorSquare.sg27288`, `OAI.UniversalTensorSquare.sg27289`, `OAI.UniversalTensorSquare.sg27292`, `OAI.UniversalTensorSquare.sg27300`, `OAI.UniversalTensorSquare.sg27302`, `OAI.UniversalTensorSquare.sg27303`, `OAI.UniversalTensorSquare.sg27308`, `OAI.UniversalTensorSquare.sg27310`, `OAI.UniversalTensorSquare.sg27312`, `OAI.UniversalTensorSquare.sg27313`, `OAI.UniversalTensorSquare.sg27321`, `OAI.UniversalTensorSquare.sg27323`, `OAI.UniversalTensorSquare.sg27324`, `OAI.UniversalTensorSquare.sg27329`, `OAI.UniversalTensorSquare.sg27333`, `OAI.UniversalTensorSquare.sg27336`, `OAI.UniversalTensorSquare.sg27338`, `OAI.UniversalTensorSquare.sg27342`, `OAI.UniversalTensorSquare.sg27345`, `OAI.UniversalTensorSquare.sg27347`, `OAI.UniversalTensorSquare.sg27349`, `OAI.UniversalTensorSquare.sg27352`, `OAI.UniversalTensorSquare.sg27358`, `OAI.UniversalTensorSquare.sg27362`, `OAI.UniversalTensorSquare.sg27364`, `OAI.UniversalTensorSquare.sg27365`, `OAI.UniversalTensorSquare.sg27368`, `OAI.UniversalTensorSquare.sg27370`, `OAI.UniversalTensorSquare.sg27371`, `OAI.UniversalTensorSquare.sg27373`, `OAI.UniversalTensorSquare.sg27379`, `OAI.UniversalTensorSquare.sg27382`, `OAI.UniversalTensorSquare.sg27383`, `OAI.UniversalTensorSquare.sg27384`, `OAI.UniversalTensorSquare.sg27387`, `OAI.UniversalTensorSquare.sg27391`, `OAI.UniversalTensorSquare.sg27394`, `OAI.UniversalTensorSquare.sg27400`, `OAI.UniversalTensorSquare.sg27408`, `OAI.UniversalTensorSquare.sg27409`, `OAI.UniversalTensorSquare.sg27410`, `OAI.UniversalTensorSquare.sg27412`, `OAI.UniversalTensorSquare.sg27414`, `OAI.UniversalTensorSquare.sg27415`, `OAI.UniversalTensorSquare.sg27416`, `OAI.UniversalTensorSquare.sg27420`, `OAI.UniversalTensorSquare.sg27422`, `OAI.UniversalTensorSquare.sg27426`, `OAI.UniversalTensorSquare.sg27430`, `OAI.UniversalTensorSquare.sg27437`, `OAI.UniversalTensorSquare.sg27438`, `OAI.UniversalTensorSquare.sg27443`, `OAI.UniversalTensorSquare.sg27448`, `OAI.UniversalTensorSquare.sg27452`, `OAI.UniversalTensorSquare.sg27453`, `OAI.UniversalTensorSquare.sg27458`, `OAI.UniversalTensorSquare.sg27462`, `OAI.UniversalTensorSquare.sg27463`, `OAI.UniversalTensorSquare.sg27464`, `OAI.UniversalTensorSquare.sg27465`, `OAI.UniversalTensorSquare.sg27466`, `OAI.UniversalTensorSquare.sg27468`, `OAI.UniversalTensorSquare.sg27469`, `OAI.UniversalTensorSquare.sg27471`, `OAI.UniversalTensorSquare.sg27473`, `OAI.UniversalTensorSquare.sg27475`, `OAI.UniversalTensorSquare.sg27476`, `OAI.UniversalTensorSquare.sg27477`, `OAI.UniversalTensorSquare.sg27479`, `OAI.UniversalTensorSquare.sg27484`, `OAI.UniversalTensorSquare.sg27485`, `OAI.UniversalTensorSquare.sg27486`, `OAI.UniversalTensorSquare.sg27488`, `OAI.UniversalTensorSquare.sg27490`, `OAI.UniversalTensorSquare.sg27491`, `OAI.UniversalTensorSquare.sg27493`, `OAI.UniversalTensorSquare.sg27498`, `OAI.UniversalTensorSquare.sg27500`, `OAI.UniversalTensorSquare.sg27501`, `OAI.UniversalTensorSquare.sg27503`, `OAI.UniversalTensorSquare.sg27524`, `OAI.UniversalTensorSquare.sg27530`, `OAI.UniversalTensorSquare.sg27535`, `OAI.UniversalTensorSquare.sg27539`, `OAI.UniversalTensorSquare.sg27541`, `OAI.UniversalTensorSquare.sg27543`, `OAI.UniversalTensorSquare.sg27575`, `OAI.UniversalTensorSquare.sg27578`, `OAI.UniversalTensorSquare.sg2758`, `OAI.UniversalTensorSquare.sg27581`, `OAI.UniversalTensorSquare.sg27636`, `OAI.UniversalTensorSquare.sg27638`, `OAI.UniversalTensorSquare.sg27640`, `OAI.UniversalTensorSquare.sg27708`, `OAI.UniversalTensorSquare.sg27856`, `OAI.UniversalTensorSquare.sg27859`, `OAI.UniversalTensorSquare.sg27955`, `OAI.UniversalTensorSquare.sg27956`, `OAI.UniversalTensorSquare.sg27958`, `OAI.UniversalTensorSquare.sg28004`, `OAI.UniversalTensorSquare.sg28005`, `OAI.UniversalTensorSquare.sg28007`, `OAI.UniversalTensorSquare.sg28041`, `OAI.UniversalTensorSquare.sg28042`, `OAI.UniversalTensorSquare.sg28044`, `OAI.UniversalTensorSquare.sg28068`, `OAI.UniversalTensorSquare.sg28083`, `OAI.UniversalTensorSquare.sg28095`, `OAI.UniversalTensorSquare.sg28113`, `OAI.UniversalTensorSquare.sg28128`, `OAI.UniversalTensorSquare.sg28139`, `OAI.UniversalTensorSquare.sg28237`, `OAI.UniversalTensorSquare.sg28246`, `OAI.UniversalTensorSquare.sg28248`, `OAI.UniversalTensorSquare.sg28276`, `OAI.UniversalTensorSquare.sg28282`, `OAI.UniversalTensorSquare.sg28283`, `OAI.UniversalTensorSquare.sg28306`, `OAI.UniversalTensorSquare.sg28309`, `OAI.UniversalTensorSquare.sg28326`, `OAI.UniversalTensorSquare.sg28359`, `OAI.UniversalTensorSquare.sg28360`, `OAI.UniversalTensorSquare.sg28368`, `OAI.UniversalTensorSquare.sg28370`, `OAI.UniversalTensorSquare.sg28372`, `OAI.UniversalTensorSquare.sg28374`, `OAI.UniversalTensorSquare.sg28380`, `OAI.UniversalTensorSquare.sg28381`, `OAI.UniversalTensorSquare.sg28383`, `OAI.UniversalTensorSquare.sg28387`, `OAI.UniversalTensorSquare.sg28388`, `OAI.UniversalTensorSquare.sg28390`, `OAI.UniversalTensorSquare.sg28391`, `OAI.UniversalTensorSquare.sg28397`, `OAI.UniversalTensorSquare.sg28399`, `OAI.UniversalTensorSquare.sg28450`, `OAI.UniversalTensorSquare.sg28458`, `OAI.UniversalTensorSquare.sg28459`, `OAI.UniversalTensorSquare.sg28474`, `OAI.UniversalTensorSquare.sg28494`, `OAI.UniversalTensorSquare.sg28495`, `OAI.UniversalTensorSquare.sg28496`, `OAI.UniversalTensorSquare.sg28505`, `OAI.UniversalTensorSquare.sg28506`, `OAI.UniversalTensorSquare.sg28509`, `OAI.UniversalTensorSquare.sg28539`, `OAI.UniversalTensorSquare.sg28540`, `OAI.UniversalTensorSquare.sg28546`, `OAI.UniversalTensorSquare.sg28563`, `OAI.UniversalTensorSquare.sg28564`, `OAI.UniversalTensorSquare.sg28572`, `OAI.UniversalTensorSquare.sg28575`, `OAI.UniversalTensorSquare.sg28584`, `OAI.UniversalTensorSquare.sg28605`, `OAI.UniversalTensorSquare.sg28622`, `OAI.UniversalTensorSquare.sg28643`, `OAI.UniversalTensorSquare.sg28654`, `OAI.UniversalTensorSquare.sg28659`, `OAI.UniversalTensorSquare.sg28662`, `OAI.UniversalTensorSquare.sg28667`, `OAI.UniversalTensorSquare.sg28688`, `OAI.UniversalTensorSquare.sg28695`, `OAI.UniversalTensorSquare.sg28697`, `OAI.UniversalTensorSquare.sg28714`, `OAI.UniversalTensorSquare.sg28741`, `OAI.UniversalTensorSquare.sg28753`, `OAI.UniversalTensorSquare.sg28759`, `OAI.UniversalTensorSquare.sg28761`, `OAI.UniversalTensorSquare.sg28766`, `OAI.UniversalTensorSquare.sg28768`, `OAI.UniversalTensorSquare.sg28769`, `OAI.UniversalTensorSquare.sg28775`, `OAI.UniversalTensorSquare.sg28780`, `OAI.UniversalTensorSquare.sg28788`, `OAI.UniversalTensorSquare.sg28791`, `OAI.UniversalTensorSquare.sg28792`, `OAI.UniversalTensorSquare.sg28796`, `OAI.UniversalTensorSquare.sg28808`, `OAI.UniversalTensorSquare.sg28819`, `OAI.UniversalTensorSquare.sg28822`, `OAI.UniversalTensorSquare.sg28826`, `OAI.UniversalTensorSquare.sg28827`, `OAI.UniversalTensorSquare.sg28833`, `OAI.UniversalTensorSquare.sg28840`, `OAI.UniversalTensorSquare.sg28841`, `OAI.UniversalTensorSquare.sg28847`, `OAI.UniversalTensorSquare.sg28848`, `OAI.UniversalTensorSquare.sg28849`, `OAI.UniversalTensorSquare.sg28850`, `OAI.UniversalTensorSquare.sg28851`, `OAI.UniversalTensorSquare.sg28853`, `OAI.UniversalTensorSquare.sg28894`, `OAI.UniversalTensorSquare.sg28898`, `OAI.UniversalTensorSquare.sg28907`, `OAI.UniversalTensorSquare.sg28920`, `OAI.UniversalTensorSquare.sg28943`, `OAI.UniversalTensorSquare.sg28954`, `OAI.UniversalTensorSquare.sg28987`, `OAI.UniversalTensorSquare.sg28988`, `OAI.UniversalTensorSquare.sg29001`, `OAI.UniversalTensorSquare.sg29008`, `OAI.UniversalTensorSquare.sg29010`, `OAI.UniversalTensorSquare.sg29014`, `OAI.UniversalTensorSquare.sg29030`, `OAI.UniversalTensorSquare.sg29036`, `OAI.UniversalTensorSquare.sg29037`, `OAI.UniversalTensorSquare.sg29038`, `OAI.UniversalTensorSquare.sg29047`, `OAI.UniversalTensorSquare.sg29051`, `OAI.UniversalTensorSquare.sg29056`, `OAI.UniversalTensorSquare.sg29057`, `OAI.UniversalTensorSquare.sg29073`, `OAI.UniversalTensorSquare.sg29088`, `OAI.UniversalTensorSquare.sg29089`, `OAI.UniversalTensorSquare.sg2909`, `OAI.UniversalTensorSquare.sg29090`, `OAI.UniversalTensorSquare.sg29098`, `OAI.UniversalTensorSquare.sg29104`, `OAI.UniversalTensorSquare.sg29106`, `OAI.UniversalTensorSquare.sg29115`, `OAI.UniversalTensorSquare.sg2912`, `OAI.UniversalTensorSquare.sg29125`, `OAI.UniversalTensorSquare.sg29128`, `OAI.UniversalTensorSquare.sg29130`, `OAI.UniversalTensorSquare.sg29132`, `OAI.UniversalTensorSquare.sg29137`, `OAI.UniversalTensorSquare.sg29164`, `OAI.UniversalTensorSquare.sg29166`, `OAI.UniversalTensorSquare.sg29175`, `OAI.UniversalTensorSquare.sg29176`, `OAI.UniversalTensorSquare.sg29183`, `OAI.UniversalTensorSquare.sg29184`, `OAI.UniversalTensorSquare.sg29191`, `OAI.UniversalTensorSquare.sg29192`, `OAI.UniversalTensorSquare.sg29194`, `OAI.UniversalTensorSquare.sg29219`, `OAI.UniversalTensorSquare.sg29220`, `OAI.UniversalTensorSquare.sg29232`, `OAI.UniversalTensorSquare.sg29238`, `OAI.UniversalTensorSquare.sg29239`, `OAI.UniversalTensorSquare.sg29243`, `OAI.UniversalTensorSquare.sg29259`, `OAI.UniversalTensorSquare.sg29260`, `OAI.UniversalTensorSquare.sg29270`, `OAI.UniversalTensorSquare.sg29271`, `OAI.UniversalTensorSquare.sg29272`, `OAI.UniversalTensorSquare.sg29274`, `OAI.UniversalTensorSquare.sg29278`, `OAI.UniversalTensorSquare.sg29282`, `OAI.UniversalTensorSquare.sg29284`, `OAI.UniversalTensorSquare.sg29287`, `OAI.UniversalTensorSquare.sg29291`, `OAI.UniversalTensorSquare.sg29292`, `OAI.UniversalTensorSquare.sg29297`, `OAI.UniversalTensorSquare.sg29303`, `OAI.UniversalTensorSquare.sg29324`, `OAI.UniversalTensorSquare.sg29325`, `OAI.UniversalTensorSquare.sg29329`, `OAI.UniversalTensorSquare.sg29330`, `OAI.UniversalTensorSquare.sg29331`, `OAI.UniversalTensorSquare.sg29332`, `OAI.UniversalTensorSquare.sg29356`, `OAI.UniversalTensorSquare.sg29363`, `OAI.UniversalTensorSquare.sg29364`, `OAI.UniversalTensorSquare.sg29366`, `OAI.UniversalTensorSquare.sg29370`, `OAI.UniversalTensorSquare.sg29390`, `OAI.UniversalTensorSquare.sg29391`, `OAI.UniversalTensorSquare.sg29392`, `OAI.UniversalTensorSquare.sg29393`, `OAI.UniversalTensorSquare.sg29399`, `OAI.UniversalTensorSquare.sg29404`, `OAI.UniversalTensorSquare.sg29409`, `OAI.UniversalTensorSquare.sg29415`, `OAI.UniversalTensorSquare.sg29420`, `OAI.UniversalTensorSquare.sg29421`, `OAI.UniversalTensorSquare.sg29424`, `OAI.UniversalTensorSquare.sg29432`, `OAI.UniversalTensorSquare.sg29433`, `OAI.UniversalTensorSquare.sg29435`, `OAI.UniversalTensorSquare.sg29444`, `OAI.UniversalTensorSquare.sg29446`, `OAI.UniversalTensorSquare.sg29447`, `OAI.UniversalTensorSquare.sg29448`, `OAI.UniversalTensorSquare.sg29452`, `OAI.UniversalTensorSquare.sg29453`, `OAI.UniversalTensorSquare.sg29454`, `OAI.UniversalTensorSquare.sg29456`, `OAI.UniversalTensorSquare.sg29457`, `OAI.UniversalTensorSquare.sg29465`, `OAI.UniversalTensorSquare.sg29477`, `OAI.UniversalTensorSquare.sg29478`, `OAI.UniversalTensorSquare.sg29480`, `OAI.UniversalTensorSquare.sg29481`, `OAI.UniversalTensorSquare.sg29486`, `OAI.UniversalTensorSquare.sg29489`, `OAI.UniversalTensorSquare.sg29495`, `OAI.UniversalTensorSquare.sg29496`, `OAI.UniversalTensorSquare.sg29503`, `OAI.UniversalTensorSquare.sg29505`, `OAI.UniversalTensorSquare.sg29507`, `OAI.UniversalTensorSquare.sg29508`, `OAI.UniversalTensorSquare.sg29509`, `OAI.UniversalTensorSquare.sg29510`, `OAI.UniversalTensorSquare.sg29518`, `OAI.UniversalTensorSquare.sg29519`, `OAI.UniversalTensorSquare.sg29520`, `OAI.UniversalTensorSquare.sg29521`, `OAI.UniversalTensorSquare.sg29522`, `OAI.UniversalTensorSquare.sg29524`, `OAI.UniversalTensorSquare.sg29525`, `OAI.UniversalTensorSquare.sg29528`, `OAI.UniversalTensorSquare.sg29529`, `OAI.UniversalTensorSquare.sg29555`, `OAI.UniversalTensorSquare.sg29556`, `OAI.UniversalTensorSquare.sg29557`, `OAI.UniversalTensorSquare.sg29558`, `OAI.UniversalTensorSquare.sg29560`, `OAI.UniversalTensorSquare.sg29563`, `OAI.UniversalTensorSquare.sg29564`, `OAI.UniversalTensorSquare.sg29568`, `OAI.UniversalTensorSquare.sg29569`, `OAI.UniversalTensorSquare.sg29582`, `OAI.UniversalTensorSquare.sg29583`, `OAI.UniversalTensorSquare.sg29589`, `OAI.UniversalTensorSquare.sg29590`, `OAI.UniversalTensorSquare.sg29594`, `OAI.UniversalTensorSquare.sg29609`, `OAI.UniversalTensorSquare.sg29610`, `OAI.UniversalTensorSquare.sg29616`, `OAI.UniversalTensorSquare.sg29633`, `OAI.UniversalTensorSquare.sg29634`, `OAI.UniversalTensorSquare.sg29636`, `OAI.UniversalTensorSquare.sg29639`, `OAI.UniversalTensorSquare.sg29640`, `OAI.UniversalTensorSquare.sg29646`, `OAI.UniversalTensorSquare.sg29647`, `OAI.UniversalTensorSquare.sg29650`, `OAI.UniversalTensorSquare.sg29652`, `OAI.UniversalTensorSquare.sg29660`, `OAI.UniversalTensorSquare.sg29663`, `OAI.UniversalTensorSquare.sg29664`, `OAI.UniversalTensorSquare.sg29667`, `OAI.UniversalTensorSquare.sg29681`, `OAI.UniversalTensorSquare.sg29684`, `OAI.UniversalTensorSquare.sg29685`, `OAI.UniversalTensorSquare.sg29694`, `OAI.UniversalTensorSquare.sg29696`, `OAI.UniversalTensorSquare.sg29697`, `OAI.UniversalTensorSquare.sg29700`, `OAI.UniversalTensorSquare.sg29704`, `OAI.UniversalTensorSquare.sg29705`, `OAI.UniversalTensorSquare.sg29706`, `OAI.UniversalTensorSquare.sg29711`, `OAI.UniversalTensorSquare.sg29712`, `OAI.UniversalTensorSquare.sg29723`, `OAI.UniversalTensorSquare.sg29725`, `OAI.UniversalTensorSquare.sg29726`, `OAI.UniversalTensorSquare.sg29731`, `OAI.UniversalTensorSquare.sg29733`, `OAI.UniversalTensorSquare.sg29734`, `OAI.UniversalTensorSquare.sg29735`, `OAI.UniversalTensorSquare.sg29737`, `OAI.UniversalTensorSquare.sg29738`, `OAI.UniversalTensorSquare.sg29739`, `OAI.UniversalTensorSquare.sg29740`, `OAI.UniversalTensorSquare.sg29744`, `OAI.UniversalTensorSquare.sg29745`, `OAI.UniversalTensorSquare.sg29746`, `OAI.UniversalTensorSquare.sg29749`, `OAI.UniversalTensorSquare.sg29750`, `OAI.UniversalTensorSquare.sg29754`, `OAI.UniversalTensorSquare.sg29755`, `OAI.UniversalTensorSquare.sg29756`, `OAI.UniversalTensorSquare.sg29779`, `OAI.UniversalTensorSquare.sg29785`, `OAI.UniversalTensorSquare.sg29800`, `OAI.UniversalTensorSquare.sg29801`, `OAI.UniversalTensorSquare.sg29807`, `OAI.UniversalTensorSquare.sg29808`, `OAI.UniversalTensorSquare.sg29813`, `OAI.UniversalTensorSquare.sg29821`, `OAI.UniversalTensorSquare.sg29824`, `OAI.UniversalTensorSquare.sg29825`, `OAI.UniversalTensorSquare.sg29826`, `OAI.UniversalTensorSquare.sg29830`, `OAI.UniversalTensorSquare.sg29835`, `OAI.UniversalTensorSquare.sg29840`, `OAI.UniversalTensorSquare.sg29844`, `OAI.UniversalTensorSquare.sg29847`, `OAI.UniversalTensorSquare.sg29848`, `OAI.UniversalTensorSquare.sg29854`, `OAI.UniversalTensorSquare.sg29855`, `OAI.UniversalTensorSquare.sg29864`, `OAI.UniversalTensorSquare.sg29865`, `OAI.UniversalTensorSquare.sg29869`, `OAI.UniversalTensorSquare.sg29876`, `OAI.UniversalTensorSquare.sg29883`, `OAI.UniversalTensorSquare.sg29885`, `OAI.UniversalTensorSquare.sg29909`, `OAI.UniversalTensorSquare.sg29914`, `OAI.UniversalTensorSquare.sg29916`, `OAI.UniversalTensorSquare.sg29919`, `OAI.UniversalTensorSquare.sg29924`, `OAI.UniversalTensorSquare.sg29928`, `OAI.UniversalTensorSquare.sg29929`, `OAI.UniversalTensorSquare.sg29949`, `OAI.UniversalTensorSquare.sg29951`, `OAI.UniversalTensorSquare.sg29981`, `OAI.UniversalTensorSquare.sg29994`, `OAI.UniversalTensorSquare.sg29999`, `OAI.UniversalTensorSquare.sg30004`, `OAI.UniversalTensorSquare.sg30034`, `OAI.UniversalTensorSquare.sg30036`, `OAI.UniversalTensorSquare.sg30039`, `OAI.UniversalTensorSquare.sg30042`, `OAI.UniversalTensorSquare.sg30045`, `OAI.UniversalTensorSquare.sg30046`, `OAI.UniversalTensorSquare.sg30047`, `OAI.UniversalTensorSquare.sg30048`, `OAI.UniversalTensorSquare.sg30058`, `OAI.UniversalTensorSquare.sg30062`, `OAI.UniversalTensorSquare.sg30064`, `OAI.UniversalTensorSquare.sg30067`, `OAI.UniversalTensorSquare.sg30071`, `OAI.UniversalTensorSquare.sg30074`, `OAI.UniversalTensorSquare.sg30075`, `OAI.UniversalTensorSquare.sg30076`, `OAI.UniversalTensorSquare.sg30077`, `OAI.UniversalTensorSquare.sg30078`, `OAI.UniversalTensorSquare.sg30083`, `OAI.UniversalTensorSquare.sg30085`, `OAI.UniversalTensorSquare.sg30088`, `OAI.UniversalTensorSquare.sg30094`, `OAI.UniversalTensorSquare.sg30095`, `OAI.UniversalTensorSquare.sg30099`, `OAI.UniversalTensorSquare.sg30122`, `OAI.UniversalTensorSquare.sg30124`, `OAI.UniversalTensorSquare.sg30125`, `OAI.UniversalTensorSquare.sg30127`, `OAI.UniversalTensorSquare.sg30144`, `OAI.UniversalTensorSquare.sg30151`, `OAI.UniversalTensorSquare.sg30154`, `OAI.UniversalTensorSquare.sg30157`, `OAI.UniversalTensorSquare.sg30163`, `OAI.UniversalTensorSquare.sg30165`, `OAI.UniversalTensorSquare.sg30176`, `OAI.UniversalTensorSquare.sg30179`, `OAI.UniversalTensorSquare.sg30182`, `OAI.UniversalTensorSquare.sg30183`, `OAI.UniversalTensorSquare.sg30184`, `OAI.UniversalTensorSquare.sg30188`, `OAI.UniversalTensorSquare.sg30192`, `OAI.UniversalTensorSquare.sg30196`, `OAI.UniversalTensorSquare.sg30200`, `OAI.UniversalTensorSquare.sg30203`, `OAI.UniversalTensorSquare.sg30204`, `OAI.UniversalTensorSquare.sg30210`, `OAI.UniversalTensorSquare.sg30218`, `OAI.UniversalTensorSquare.sg30233`, `OAI.UniversalTensorSquare.sg30234`, `OAI.UniversalTensorSquare.sg30235`, `OAI.UniversalTensorSquare.sg30240`, `OAI.UniversalTensorSquare.sg30241`, `OAI.UniversalTensorSquare.sg30244`, `OAI.UniversalTensorSquare.sg30246`, `OAI.UniversalTensorSquare.sg30247`, `OAI.UniversalTensorSquare.sg30249`, `OAI.UniversalTensorSquare.sg30255`, `OAI.UniversalTensorSquare.sg30257`, `OAI.UniversalTensorSquare.sg30258`, `OAI.UniversalTensorSquare.sg30259`, `OAI.UniversalTensorSquare.sg30261`, `OAI.UniversalTensorSquare.sg30269`, `OAI.UniversalTensorSquare.sg30271`, `OAI.UniversalTensorSquare.sg30274`, `OAI.UniversalTensorSquare.sg30277`, `OAI.UniversalTensorSquare.sg30278`, `OAI.UniversalTensorSquare.sg30283`, `OAI.UniversalTensorSquare.sg30286`, `OAI.UniversalTensorSquare.sg30289`, `OAI.UniversalTensorSquare.sg30292`, `OAI.UniversalTensorSquare.sg30293`, `OAI.UniversalTensorSquare.sg30300`, `OAI.UniversalTensorSquare.sg30308`, `OAI.UniversalTensorSquare.sg30311`, `OAI.UniversalTensorSquare.sg30312`, `OAI.UniversalTensorSquare.sg30315`, `OAI.UniversalTensorSquare.sg30320`, `OAI.UniversalTensorSquare.sg30324`, `OAI.UniversalTensorSquare.sg30326`, `OAI.UniversalTensorSquare.sg30336`, `OAI.UniversalTensorSquare.sg30337`, `OAI.UniversalTensorSquare.sg30343`, `OAI.UniversalTensorSquare.sg30347`, `OAI.UniversalTensorSquare.sg30350`, `OAI.UniversalTensorSquare.sg30352`, `OAI.UniversalTensorSquare.sg30358`, `OAI.UniversalTensorSquare.sg30360`, `OAI.UniversalTensorSquare.sg30372`, `OAI.UniversalTensorSquare.sg30377`, `OAI.UniversalTensorSquare.sg30378`, `OAI.UniversalTensorSquare.sg30382`, `OAI.UniversalTensorSquare.sg30383`, `OAI.UniversalTensorSquare.sg30389`, `OAI.UniversalTensorSquare.sg30393`, `OAI.UniversalTensorSquare.sg30400`, `OAI.UniversalTensorSquare.sg30401`, `OAI.UniversalTensorSquare.sg30429`, `OAI.UniversalTensorSquare.sg30430`, `OAI.UniversalTensorSquare.sg30433`, `OAI.UniversalTensorSquare.sg30435`, `OAI.UniversalTensorSquare.sg30442`, `OAI.UniversalTensorSquare.sg30443`, `OAI.UniversalTensorSquare.sg30445`, `OAI.UniversalTensorSquare.sg30446`, `OAI.UniversalTensorSquare.sg30449`, `OAI.UniversalTensorSquare.sg30450`, `OAI.UniversalTensorSquare.sg30459`, `OAI.UniversalTensorSquare.sg30460`, `OAI.UniversalTensorSquare.sg30474`, `OAI.UniversalTensorSquare.sg30479`, `OAI.UniversalTensorSquare.sg30480`, `OAI.UniversalTensorSquare.sg30481`, `OAI.UniversalTensorSquare.sg30499`, `OAI.UniversalTensorSquare.sg30500`, `OAI.UniversalTensorSquare.sg30505`, `OAI.UniversalTensorSquare.sg30506`, `OAI.UniversalTensorSquare.sg30509`, `OAI.UniversalTensorSquare.sg30517`, `OAI.UniversalTensorSquare.sg30520`, `OAI.UniversalTensorSquare.sg30528`, `OAI.UniversalTensorSquare.sg30535`, `OAI.UniversalTensorSquare.sg30536`, `OAI.UniversalTensorSquare.sg30538`, `OAI.UniversalTensorSquare.sg30539`, `OAI.UniversalTensorSquare.sg30541`, `OAI.UniversalTensorSquare.sg30548`, `OAI.UniversalTensorSquare.sg30563`, `OAI.UniversalTensorSquare.sg30576`, `OAI.UniversalTensorSquare.sg30579`, `OAI.UniversalTensorSquare.sg30585`, `OAI.UniversalTensorSquare.sg30588`, `OAI.UniversalTensorSquare.sg30589`, `OAI.UniversalTensorSquare.sg30592`, `OAI.UniversalTensorSquare.sg30593`, `OAI.UniversalTensorSquare.sg30595`, `OAI.UniversalTensorSquare.sg30617`, `OAI.UniversalTensorSquare.sg30620`, `OAI.UniversalTensorSquare.sg30626`, `OAI.UniversalTensorSquare.sg30638`, `OAI.UniversalTensorSquare.sg30644`, `OAI.UniversalTensorSquare.sg30646`, `OAI.UniversalTensorSquare.sg3065`, `OAI.UniversalTensorSquare.sg30668`, `OAI.UniversalTensorSquare.sg30691`, `OAI.UniversalTensorSquare.sg30697`, `OAI.UniversalTensorSquare.sg30698`, `OAI.UniversalTensorSquare.sg30699`, `OAI.UniversalTensorSquare.sg30740`, `OAI.UniversalTensorSquare.sg30741`, `OAI.UniversalTensorSquare.sg30747`, `OAI.UniversalTensorSquare.sg30750`, `OAI.UniversalTensorSquare.sg30753`, `OAI.UniversalTensorSquare.sg30754`, `OAI.UniversalTensorSquare.sg30756`, `OAI.UniversalTensorSquare.sg30780`, `OAI.UniversalTensorSquare.sg30783`, `OAI.UniversalTensorSquare.sg30786`, `OAI.UniversalTensorSquare.sg30792`, `OAI.UniversalTensorSquare.sg30794`, `OAI.UniversalTensorSquare.sg30796`, `OAI.UniversalTensorSquare.sg30800`, `OAI.UniversalTensorSquare.sg30805`, `OAI.UniversalTensorSquare.sg30806`, `OAI.UniversalTensorSquare.sg30809`, `OAI.UniversalTensorSquare.sg30813`, `OAI.UniversalTensorSquare.sg30816`, `OAI.UniversalTensorSquare.sg30817`, `OAI.UniversalTensorSquare.sg30821`, `OAI.UniversalTensorSquare.sg30823`, `OAI.UniversalTensorSquare.sg30825`, `OAI.UniversalTensorSquare.sg30829`, `OAI.UniversalTensorSquare.sg30832`, `OAI.UniversalTensorSquare.sg30838`, `OAI.UniversalTensorSquare.sg30841`, `OAI.UniversalTensorSquare.sg30846`, `OAI.UniversalTensorSquare.sg30847`, `OAI.UniversalTensorSquare.sg30849`, `OAI.UniversalTensorSquare.sg30853`, `OAI.UniversalTensorSquare.sg30855`, `OAI.UniversalTensorSquare.sg30870`, `OAI.UniversalTensorSquare.sg30872`, `OAI.UniversalTensorSquare.sg30875`, `OAI.UniversalTensorSquare.sg30876`, `OAI.UniversalTensorSquare.sg30879`, `OAI.UniversalTensorSquare.sg30884`, `OAI.UniversalTensorSquare.sg30888`, `OAI.UniversalTensorSquare.sg30890`, `OAI.UniversalTensorSquare.sg30899`, `OAI.UniversalTensorSquare.sg30901`, `OAI.UniversalTensorSquare.sg30907`, `OAI.UniversalTensorSquare.sg30911`, `OAI.UniversalTensorSquare.sg30913`, `OAI.UniversalTensorSquare.sg30914`, `OAI.UniversalTensorSquare.sg30922`, `OAI.UniversalTensorSquare.sg30924`, `OAI.UniversalTensorSquare.sg30925`, `OAI.UniversalTensorSquare.sg30926`, `OAI.UniversalTensorSquare.sg30940`, `OAI.UniversalTensorSquare.sg30945`, `OAI.UniversalTensorSquare.sg30947`, `OAI.UniversalTensorSquare.sg30949`, `OAI.UniversalTensorSquare.sg30951`, `OAI.UniversalTensorSquare.sg30952`, `OAI.UniversalTensorSquare.sg30953`, `OAI.UniversalTensorSquare.sg30955`, `OAI.UniversalTensorSquare.sg30961`, `OAI.UniversalTensorSquare.sg30962`, `OAI.UniversalTensorSquare.sg30963`, `OAI.UniversalTensorSquare.sg30965`, `OAI.UniversalTensorSquare.sg30970`, `OAI.UniversalTensorSquare.sg30972`, `OAI.UniversalTensorSquare.sg30973`, `OAI.UniversalTensorSquare.sg30980`, `OAI.UniversalTensorSquare.sg30981`, `OAI.UniversalTensorSquare.sg30989`, `OAI.UniversalTensorSquare.sg30991`, `OAI.UniversalTensorSquare.sg30992`, `OAI.UniversalTensorSquare.sg30993`, `OAI.UniversalTensorSquare.sg30997`, `OAI.UniversalTensorSquare.sg30999`, `OAI.UniversalTensorSquare.sg31003`, `OAI.UniversalTensorSquare.sg31005`, `OAI.UniversalTensorSquare.sg31012`, `OAI.UniversalTensorSquare.sg31020`, `OAI.UniversalTensorSquare.sg31022`, `OAI.UniversalTensorSquare.sg31024`, `OAI.UniversalTensorSquare.sg31030`, `OAI.UniversalTensorSquare.sg31032`, `OAI.UniversalTensorSquare.sg31042`, `OAI.UniversalTensorSquare.sg31058`, `OAI.UniversalTensorSquare.sg31060`, `OAI.UniversalTensorSquare.sg31072`, `OAI.UniversalTensorSquare.sg31076`, `OAI.UniversalTensorSquare.sg31077`, `OAI.UniversalTensorSquare.sg31078`, `OAI.UniversalTensorSquare.sg31082`, `OAI.UniversalTensorSquare.sg31085`, `OAI.UniversalTensorSquare.sg31086`, `OAI.UniversalTensorSquare.sg31087`, `OAI.UniversalTensorSquare.sg31091`, `OAI.UniversalTensorSquare.sg31094`, `OAI.UniversalTensorSquare.sg31095`, `OAI.UniversalTensorSquare.sg31096`, `OAI.UniversalTensorSquare.sg31100`, `OAI.UniversalTensorSquare.sg31102`, `OAI.UniversalTensorSquare.sg31138`, `OAI.UniversalTensorSquare.sg31140`, `OAI.UniversalTensorSquare.sg31141`, `OAI.UniversalTensorSquare.sg31145`, `OAI.UniversalTensorSquare.sg31147`, `OAI.UniversalTensorSquare.sg31149`, `OAI.UniversalTensorSquare.sg31153`, `OAI.UniversalTensorSquare.sg31155`, `OAI.UniversalTensorSquare.sg31156`, `OAI.UniversalTensorSquare.sg31157`, `OAI.UniversalTensorSquare.sg31159`, `OAI.UniversalTensorSquare.sg31161`, `OAI.UniversalTensorSquare.sg31162`, `OAI.UniversalTensorSquare.sg31163`, `OAI.UniversalTensorSquare.sg31180`, `OAI.UniversalTensorSquare.sg31184`, `OAI.UniversalTensorSquare.sg31196`, `OAI.UniversalTensorSquare.sg31198`, `OAI.UniversalTensorSquare.sg31200`, `OAI.UniversalTensorSquare.sg31203`, `OAI.UniversalTensorSquare.sg31206`, `OAI.UniversalTensorSquare.sg31208`, `OAI.UniversalTensorSquare.sg31210`, `OAI.UniversalTensorSquare.sg31211`, `OAI.UniversalTensorSquare.sg31212`, `OAI.UniversalTensorSquare.sg31213`, `OAI.UniversalTensorSquare.sg31214`, `OAI.UniversalTensorSquare.sg31215`, `OAI.UniversalTensorSquare.sg31216`, `OAI.UniversalTensorSquare.sg31217`, `OAI.UniversalTensorSquare.sg31218`, `OAI.UniversalTensorSquare.sg31219`, `OAI.UniversalTensorSquare.sg31220`, `OAI.UniversalTensorSquare.sg31221`, `OAI.UniversalTensorSquare.sg31223`, `OAI.UniversalTensorSquare.sg31224`, `OAI.UniversalTensorSquare.sg31225`, `OAI.UniversalTensorSquare.sg31228`, `OAI.UniversalTensorSquare.sg31229`, `OAI.UniversalTensorSquare.sg31231`, `OAI.UniversalTensorSquare.sg31233`, `OAI.UniversalTensorSquare.sg31236`, `OAI.UniversalTensorSquare.sg31238`, `OAI.UniversalTensorSquare.sg31240`, `OAI.UniversalTensorSquare.sg31241`, `OAI.UniversalTensorSquare.sg31242`, `OAI.UniversalTensorSquare.sg31244`, `OAI.UniversalTensorSquare.sg31245`, `OAI.UniversalTensorSquare.sg31252`, `OAI.UniversalTensorSquare.sg31254`, `OAI.UniversalTensorSquare.sg31264`, `OAI.UniversalTensorSquare.sg31270`, `OAI.UniversalTensorSquare.sg31272`, `OAI.UniversalTensorSquare.sg31273`, `OAI.UniversalTensorSquare.sg31275`, `OAI.UniversalTensorSquare.sg31280`, `OAI.UniversalTensorSquare.sg31281`, `OAI.UniversalTensorSquare.sg31286`, `OAI.UniversalTensorSquare.sg31288`, `OAI.UniversalTensorSquare.sg31291`, `OAI.UniversalTensorSquare.sg31292`, `OAI.UniversalTensorSquare.sg31294`, `OAI.UniversalTensorSquare.sg31296`, `OAI.UniversalTensorSquare.sg31298`, `OAI.UniversalTensorSquare.sg31302`, `OAI.UniversalTensorSquare.sg31303`, `OAI.UniversalTensorSquare.sg31308`, `OAI.UniversalTensorSquare.sg31311`, `OAI.UniversalTensorSquare.sg31313`, `OAI.UniversalTensorSquare.sg31316`, `OAI.UniversalTensorSquare.sg31317`, `OAI.UniversalTensorSquare.sg31318`, `OAI.UniversalTensorSquare.sg31319`, `OAI.UniversalTensorSquare.sg31320`, `OAI.UniversalTensorSquare.sg31322`, `OAI.UniversalTensorSquare.sg31325`, `OAI.UniversalTensorSquare.sg31329`, `OAI.UniversalTensorSquare.sg31333`, `OAI.UniversalTensorSquare.sg31334`, `OAI.UniversalTensorSquare.sg31335`, `OAI.UniversalTensorSquare.sg31337`, `OAI.UniversalTensorSquare.sg31339`, `OAI.UniversalTensorSquare.sg31345`, `OAI.UniversalTensorSquare.sg31346`, `OAI.UniversalTensorSquare.sg31348`, `OAI.UniversalTensorSquare.sg31357`, `OAI.UniversalTensorSquare.sg31360`, `OAI.UniversalTensorSquare.sg31361`, `OAI.UniversalTensorSquare.sg31371`, `OAI.UniversalTensorSquare.sg31372`, `OAI.UniversalTensorSquare.sg31374`, `OAI.UniversalTensorSquare.sg31375`, `OAI.UniversalTensorSquare.sg31377`, `OAI.UniversalTensorSquare.sg31379`, `OAI.UniversalTensorSquare.sg31385`, `OAI.UniversalTensorSquare.sg31386`, `OAI.UniversalTensorSquare.sg31388`, `OAI.UniversalTensorSquare.sg31391`, `OAI.UniversalTensorSquare.sg31397`, `OAI.UniversalTensorSquare.sg31398`, `OAI.UniversalTensorSquare.sg31399`, `OAI.UniversalTensorSquare.sg31404`, `OAI.UniversalTensorSquare.sg31408`, `OAI.UniversalTensorSquare.sg31414`, `OAI.UniversalTensorSquare.sg31415`, `OAI.UniversalTensorSquare.sg31417`, `OAI.UniversalTensorSquare.sg31421`, `OAI.UniversalTensorSquare.sg31422`, `OAI.UniversalTensorSquare.sg31423`, `OAI.UniversalTensorSquare.sg31424`, `OAI.UniversalTensorSquare.sg31449`, `OAI.UniversalTensorSquare.sg31455`, `OAI.UniversalTensorSquare.sg31463`, `OAI.UniversalTensorSquare.sg31467`, `OAI.UniversalTensorSquare.sg31469`, `OAI.UniversalTensorSquare.sg31472`, `OAI.UniversalTensorSquare.sg31474`, `OAI.UniversalTensorSquare.sg31476`, `OAI.UniversalTensorSquare.sg31483`, `OAI.UniversalTensorSquare.sg31495`, `OAI.UniversalTensorSquare.sg31505`, `OAI.UniversalTensorSquare.sg31506`, `OAI.UniversalTensorSquare.sg31512`, `OAI.UniversalTensorSquare.sg31515`, `OAI.UniversalTensorSquare.sg31517`, `OAI.UniversalTensorSquare.sg31519`, `OAI.UniversalTensorSquare.sg31526`, `OAI.UniversalTensorSquare.sg31529`, `OAI.UniversalTensorSquare.sg31530`, `OAI.UniversalTensorSquare.sg31531`, `OAI.UniversalTensorSquare.sg31533`, `OAI.UniversalTensorSquare.sg31543`, `OAI.UniversalTensorSquare.sg31556`, `OAI.UniversalTensorSquare.sg31557`, `OAI.UniversalTensorSquare.sg31589`, `OAI.UniversalTensorSquare.sg31596`, `OAI.UniversalTensorSquare.sg31604`, `OAI.UniversalTensorSquare.sg31605`, `OAI.UniversalTensorSquare.sg31606`, `OAI.UniversalTensorSquare.sg31607`, `OAI.UniversalTensorSquare.sg31608`, `OAI.UniversalTensorSquare.sg31639`, `OAI.UniversalTensorSquare.sg31654`, `OAI.UniversalTensorSquare.sg31666`, `OAI.UniversalTensorSquare.sg31674`, `OAI.UniversalTensorSquare.sg31675`, `OAI.UniversalTensorSquare.sg31697`, `OAI.UniversalTensorSquare.sg31708`, `OAI.UniversalTensorSquare.sg31728`, `OAI.UniversalTensorSquare.sg31730`, `OAI.UniversalTensorSquare.sg31732`, `OAI.UniversalTensorSquare.sg31749`, `OAI.UniversalTensorSquare.sg31767`, `OAI.UniversalTensorSquare.sg31776`, `OAI.UniversalTensorSquare.sg31778`, `OAI.UniversalTensorSquare.sg31779`, `OAI.UniversalTensorSquare.sg31780`, `OAI.UniversalTensorSquare.sg31790`, `OAI.UniversalTensorSquare.sg31791`, `OAI.UniversalTensorSquare.sg31792`, `OAI.UniversalTensorSquare.sg31800`, `OAI.UniversalTensorSquare.sg31801`, `OAI.UniversalTensorSquare.sg31844`, `OAI.UniversalTensorSquare.sg31845`, `OAI.UniversalTensorSquare.sg31854`, `OAI.UniversalTensorSquare.sg31856`, `OAI.UniversalTensorSquare.sg31865`, `OAI.UniversalTensorSquare.sg31887`, `OAI.UniversalTensorSquare.sg31896`, `OAI.UniversalTensorSquare.sg31901`, `OAI.UniversalTensorSquare.sg31910`, `OAI.UniversalTensorSquare.sg31920`, `OAI.UniversalTensorSquare.sg31924`, `OAI.UniversalTensorSquare.sg31934`, `OAI.UniversalTensorSquare.sg31960`, `OAI.UniversalTensorSquare.sg31969`, `OAI.UniversalTensorSquare.sg31974`, `OAI.UniversalTensorSquare.sg31979`, `OAI.UniversalTensorSquare.sg31982`, `OAI.UniversalTensorSquare.sg31983`, `OAI.UniversalTensorSquare.sg31984`, `OAI.UniversalTensorSquare.sg31996`, `OAI.UniversalTensorSquare.sg32009`, `OAI.UniversalTensorSquare.sg32022`, `OAI.UniversalTensorSquare.sg32024`, `OAI.UniversalTensorSquare.sg32025`, `OAI.UniversalTensorSquare.sg32056`, `OAI.UniversalTensorSquare.sg32063`, `OAI.UniversalTensorSquare.sg32066`, `OAI.UniversalTensorSquare.sg32068`, `OAI.UniversalTensorSquare.sg32069`, `OAI.UniversalTensorSquare.sg32072`, `OAI.UniversalTensorSquare.sg32073`, `OAI.UniversalTensorSquare.sg32079`, `OAI.UniversalTensorSquare.sg32080`, `OAI.UniversalTensorSquare.sg32081`, `OAI.UniversalTensorSquare.sg32086`, `OAI.UniversalTensorSquare.sg32092`, `OAI.UniversalTensorSquare.sg32103`, `OAI.UniversalTensorSquare.sg32107`, `OAI.UniversalTensorSquare.sg32144`, `OAI.UniversalTensorSquare.sg32145`, `OAI.UniversalTensorSquare.sg32147`, `OAI.UniversalTensorSquare.sg32149`, `OAI.UniversalTensorSquare.sg32152`, `OAI.UniversalTensorSquare.sg32167`, `OAI.UniversalTensorSquare.sg32168`, `OAI.UniversalTensorSquare.sg32169`, `OAI.UniversalTensorSquare.sg32170`, `OAI.UniversalTensorSquare.sg32172`, `OAI.UniversalTensorSquare.sg32173`, `OAI.UniversalTensorSquare.sg32175`, `OAI.UniversalTensorSquare.sg32177`, `OAI.UniversalTensorSquare.sg32178`, `OAI.UniversalTensorSquare.sg32179`, `OAI.UniversalTensorSquare.sg32180`, `OAI.UniversalTensorSquare.sg32182`, `OAI.UniversalTensorSquare.sg32183`, `OAI.UniversalTensorSquare.sg32185`, `OAI.UniversalTensorSquare.sg32187`, `OAI.UniversalTensorSquare.sg32189`, `OAI.UniversalTensorSquare.sg32190`, `OAI.UniversalTensorSquare.sg32191`, `OAI.UniversalTensorSquare.sg32192`, `OAI.UniversalTensorSquare.sg32193`, `OAI.UniversalTensorSquare.sg32194`, `OAI.UniversalTensorSquare.sg32195`, `OAI.UniversalTensorSquare.sg32196`, `OAI.UniversalTensorSquare.sg32197`, `OAI.UniversalTensorSquare.sg32198`, `OAI.UniversalTensorSquare.sg32199`, `OAI.UniversalTensorSquare.sg32202`, `OAI.UniversalTensorSquare.sg32205`, `OAI.UniversalTensorSquare.sg32214`, `OAI.UniversalTensorSquare.sg32220`, `OAI.UniversalTensorSquare.sg32227`, `OAI.UniversalTensorSquare.sg32228`, `OAI.UniversalTensorSquare.sg32229`, `OAI.UniversalTensorSquare.sg32233`, `OAI.UniversalTensorSquare.sg32235`, `OAI.UniversalTensorSquare.sg32237`, `OAI.UniversalTensorSquare.sg32239`, `OAI.UniversalTensorSquare.sg32240`, `OAI.UniversalTensorSquare.sg32243`, `OAI.UniversalTensorSquare.sg32249`, `OAI.UniversalTensorSquare.sg32250`, `OAI.UniversalTensorSquare.sg32251`, `OAI.UniversalTensorSquare.sg32255`, `OAI.UniversalTensorSquare.sg32275`, `OAI.UniversalTensorSquare.sg32277`, `OAI.UniversalTensorSquare.sg32297`, `OAI.UniversalTensorSquare.sg32299`, `OAI.UniversalTensorSquare.sg32306`, `OAI.UniversalTensorSquare.sg32319`, `OAI.UniversalTensorSquare.sg32321`, `OAI.UniversalTensorSquare.sg32323`, `OAI.UniversalTensorSquare.sg32331`, `OAI.UniversalTensorSquare.sg32347`, `OAI.UniversalTensorSquare.sg32348`, `OAI.UniversalTensorSquare.sg32349`, `OAI.UniversalTensorSquare.sg32351`, `OAI.UniversalTensorSquare.sg32352`, `OAI.UniversalTensorSquare.sg32355`, `OAI.UniversalTensorSquare.sg32358`, `OAI.UniversalTensorSquare.sg32362`, `OAI.UniversalTensorSquare.sg32363`, `OAI.UniversalTensorSquare.sg32366`, `OAI.UniversalTensorSquare.sg32372`, `OAI.UniversalTensorSquare.sg32374`, `OAI.UniversalTensorSquare.sg32386`, `OAI.UniversalTensorSquare.sg32389`, `OAI.UniversalTensorSquare.sg32390`, `OAI.UniversalTensorSquare.sg32391`, `OAI.UniversalTensorSquare.sg32392`, `OAI.UniversalTensorSquare.sg32403`, `OAI.UniversalTensorSquare.sg32405`, `OAI.UniversalTensorSquare.sg32406`, `OAI.UniversalTensorSquare.sg32418`, `OAI.UniversalTensorSquare.sg32423`, `OAI.UniversalTensorSquare.sg32424`, `OAI.UniversalTensorSquare.sg32425`, `OAI.UniversalTensorSquare.sg32426`, `OAI.UniversalTensorSquare.sg32427`, `OAI.UniversalTensorSquare.sg32429`, `OAI.UniversalTensorSquare.sg32430`, `OAI.UniversalTensorSquare.sg32431`, `OAI.UniversalTensorSquare.sg32432`, `OAI.UniversalTensorSquare.sg32433`, `OAI.UniversalTensorSquare.sg32441`, `OAI.UniversalTensorSquare.sg32451`, `OAI.UniversalTensorSquare.sg32453`, `OAI.UniversalTensorSquare.sg32455`, `OAI.UniversalTensorSquare.sg32459`, `OAI.UniversalTensorSquare.sg32463`, `OAI.UniversalTensorSquare.sg32465`, `OAI.UniversalTensorSquare.sg32471`, `OAI.UniversalTensorSquare.sg32472`, `OAI.UniversalTensorSquare.sg32482`, `OAI.UniversalTensorSquare.sg32512`, `OAI.UniversalTensorSquare.sg32513`, `OAI.UniversalTensorSquare.sg32514`, `OAI.UniversalTensorSquare.sg32516`, `OAI.UniversalTensorSquare.sg32517`, `OAI.UniversalTensorSquare.sg32519`, `OAI.UniversalTensorSquare.sg32530`, `OAI.UniversalTensorSquare.sg32536`, `OAI.UniversalTensorSquare.sg32542`, `OAI.UniversalTensorSquare.sg32553`, `OAI.UniversalTensorSquare.sg32555`, `OAI.UniversalTensorSquare.sg32557`, `OAI.UniversalTensorSquare.sg32558`, `OAI.UniversalTensorSquare.sg32560`, `OAI.UniversalTensorSquare.sg32563`, `OAI.UniversalTensorSquare.sg32564`, `OAI.UniversalTensorSquare.sg32568`, `OAI.UniversalTensorSquare.sg32569`, `OAI.UniversalTensorSquare.sg32572`, `OAI.UniversalTensorSquare.sg32578`, `OAI.UniversalTensorSquare.sg32580`, `OAI.UniversalTensorSquare.sg32589`, `OAI.UniversalTensorSquare.sg32590`, `OAI.UniversalTensorSquare.sg32593`, `OAI.UniversalTensorSquare.sg32603`, `OAI.UniversalTensorSquare.sg32606`, `OAI.UniversalTensorSquare.sg32607`, `OAI.UniversalTensorSquare.sg32609`, `OAI.UniversalTensorSquare.sg32614`, `OAI.UniversalTensorSquare.sg32616`, `OAI.UniversalTensorSquare.sg32625`, `OAI.UniversalTensorSquare.sg32626`, `OAI.UniversalTensorSquare.sg32627`, `OAI.UniversalTensorSquare.sg32628`, `OAI.UniversalTensorSquare.sg32635`, `OAI.UniversalTensorSquare.sg32636`, `OAI.UniversalTensorSquare.sg32639`, `OAI.UniversalTensorSquare.sg32641`, `OAI.UniversalTensorSquare.sg32646`, `OAI.UniversalTensorSquare.sg32647`, `OAI.UniversalTensorSquare.sg32648`, `OAI.UniversalTensorSquare.sg32652`, `OAI.UniversalTensorSquare.sg32653`, `OAI.UniversalTensorSquare.sg32654`, `OAI.UniversalTensorSquare.sg32657`, `OAI.UniversalTensorSquare.sg32659`, `OAI.UniversalTensorSquare.sg32660`, `OAI.UniversalTensorSquare.sg32666`, `OAI.UniversalTensorSquare.sg32672`, `OAI.UniversalTensorSquare.sg32673`, `OAI.UniversalTensorSquare.sg32674`, `OAI.UniversalTensorSquare.sg32676`, `OAI.UniversalTensorSquare.sg32677`, `OAI.UniversalTensorSquare.sg32679`, `OAI.UniversalTensorSquare.sg32681`, `OAI.UniversalTensorSquare.sg32684`, `OAI.UniversalTensorSquare.sg32687`, `OAI.UniversalTensorSquare.sg32689`, `OAI.UniversalTensorSquare.sg32694`, `OAI.UniversalTensorSquare.sg32695`, `OAI.UniversalTensorSquare.sg32696`, `OAI.UniversalTensorSquare.sg32697`, `OAI.UniversalTensorSquare.sg32699`, `OAI.UniversalTensorSquare.sg32700`, `OAI.UniversalTensorSquare.sg32705`, `OAI.UniversalTensorSquare.sg32706`, `OAI.UniversalTensorSquare.sg32707`, `OAI.UniversalTensorSquare.sg32710`, `OAI.UniversalTensorSquare.sg32711`, `OAI.UniversalTensorSquare.sg32712`, `OAI.UniversalTensorSquare.sg32713`, `OAI.UniversalTensorSquare.sg32715`, `OAI.UniversalTensorSquare.sg32740`, `OAI.UniversalTensorSquare.sg32741`, `OAI.UniversalTensorSquare.sg32742`, `OAI.UniversalTensorSquare.sg32766`, `OAI.UniversalTensorSquare.sg32771`, `OAI.UniversalTensorSquare.sg32774`, `OAI.UniversalTensorSquare.sg32785`, `OAI.UniversalTensorSquare.sg32787`, `OAI.UniversalTensorSquare.sg32810`, `OAI.UniversalTensorSquare.sg32812`, `OAI.UniversalTensorSquare.sg32816`, `OAI.UniversalTensorSquare.sg32821`, `OAI.UniversalTensorSquare.sg32822`, `OAI.UniversalTensorSquare.sg32823`, `OAI.UniversalTensorSquare.sg32833`, `OAI.UniversalTensorSquare.sg32848`, `OAI.UniversalTensorSquare.sg32854`, `OAI.UniversalTensorSquare.sg32862`, `OAI.UniversalTensorSquare.sg32864`, `OAI.UniversalTensorSquare.sg32901`, `OAI.UniversalTensorSquare.sg32904`, `OAI.UniversalTensorSquare.sg32910`, `OAI.UniversalTensorSquare.sg32912`, `OAI.UniversalTensorSquare.sg32914`, `OAI.UniversalTensorSquare.sg32916`, `OAI.UniversalTensorSquare.sg32918`, `OAI.UniversalTensorSquare.sg32922`, `OAI.UniversalTensorSquare.sg32923`, `OAI.UniversalTensorSquare.sg32924`, `OAI.UniversalTensorSquare.sg32926`, `OAI.UniversalTensorSquare.sg32953`, `OAI.UniversalTensorSquare.sg32954`, `OAI.UniversalTensorSquare.sg32957`, `OAI.UniversalTensorSquare.sg32961`, `OAI.UniversalTensorSquare.sg32963`, `OAI.UniversalTensorSquare.sg32967`, `OAI.UniversalTensorSquare.sg32968`, `OAI.UniversalTensorSquare.sg32970`, `OAI.UniversalTensorSquare.sg32974`, `OAI.UniversalTensorSquare.sg32976`, `OAI.UniversalTensorSquare.sg32977`, `OAI.UniversalTensorSquare.sg32981`, `OAI.UniversalTensorSquare.sg32990`, `OAI.UniversalTensorSquare.sg32991`, `OAI.UniversalTensorSquare.sg32992`, `OAI.UniversalTensorSquare.sg32994`, `OAI.UniversalTensorSquare.sg32996`, `OAI.UniversalTensorSquare.sg32997`, `OAI.UniversalTensorSquare.sg32998`, `OAI.UniversalTensorSquare.sg33001`, `OAI.UniversalTensorSquare.sg33008`, `OAI.UniversalTensorSquare.sg33009`, `OAI.UniversalTensorSquare.sg33011`, `OAI.UniversalTensorSquare.sg33015`, `OAI.UniversalTensorSquare.sg33016`, `OAI.UniversalTensorSquare.sg33018`, `OAI.UniversalTensorSquare.sg33019`, `OAI.UniversalTensorSquare.sg33023`, `OAI.UniversalTensorSquare.sg33032`, `OAI.UniversalTensorSquare.sg33034`, `OAI.UniversalTensorSquare.sg33036`, `OAI.UniversalTensorSquare.sg33037`, `OAI.UniversalTensorSquare.sg33054`, `OAI.UniversalTensorSquare.sg33056`, `OAI.UniversalTensorSquare.sg33057`, `OAI.UniversalTensorSquare.sg33060`, `OAI.UniversalTensorSquare.sg33061`, `OAI.UniversalTensorSquare.sg33066`, `OAI.UniversalTensorSquare.sg33069`, `OAI.UniversalTensorSquare.sg33070`, `OAI.UniversalTensorSquare.sg33073`, `OAI.UniversalTensorSquare.sg33077`, `OAI.UniversalTensorSquare.sg33079`, `OAI.UniversalTensorSquare.sg33086`, `OAI.UniversalTensorSquare.sg33090`, `OAI.UniversalTensorSquare.sg33092`, `OAI.UniversalTensorSquare.sg33100`, `OAI.UniversalTensorSquare.sg33101`, `OAI.UniversalTensorSquare.sg33110`, `OAI.UniversalTensorSquare.sg33113`, `OAI.UniversalTensorSquare.sg33125`, `OAI.UniversalTensorSquare.sg33127`, `OAI.UniversalTensorSquare.sg33134`, `OAI.UniversalTensorSquare.sg33139`, `OAI.UniversalTensorSquare.sg33142`, `OAI.UniversalTensorSquare.sg33144`, `OAI.UniversalTensorSquare.sg33145`, `OAI.UniversalTensorSquare.sg33152`, `OAI.UniversalTensorSquare.sg33155`, `OAI.UniversalTensorSquare.sg33156`, `OAI.UniversalTensorSquare.sg33158`, `OAI.UniversalTensorSquare.sg33167`, `OAI.UniversalTensorSquare.sg33169`, `OAI.UniversalTensorSquare.sg33173`, `OAI.UniversalTensorSquare.sg33179`, `OAI.UniversalTensorSquare.sg33180`, `OAI.UniversalTensorSquare.sg33183`, `OAI.UniversalTensorSquare.sg33185`, `OAI.UniversalTensorSquare.sg33186`, `OAI.UniversalTensorSquare.sg33189`, `OAI.UniversalTensorSquare.sg33198`, `OAI.UniversalTensorSquare.sg33200`, `OAI.UniversalTensorSquare.sg33207`, `OAI.UniversalTensorSquare.sg33215`, `OAI.UniversalTensorSquare.sg33217`, `OAI.UniversalTensorSquare.sg33232`, `OAI.UniversalTensorSquare.sg33233`, `OAI.UniversalTensorSquare.sg33234`, `OAI.UniversalTensorSquare.sg33236`, `OAI.UniversalTensorSquare.sg33237`, `OAI.UniversalTensorSquare.sg33239`, `OAI.UniversalTensorSquare.sg33244`, `OAI.UniversalTensorSquare.sg33246`, `OAI.UniversalTensorSquare.sg33254`, `OAI.UniversalTensorSquare.sg33275`, `OAI.UniversalTensorSquare.sg33280`, `OAI.UniversalTensorSquare.sg33283`, `OAI.UniversalTensorSquare.sg33292`, `OAI.UniversalTensorSquare.sg33310`, `OAI.UniversalTensorSquare.sg33315`, `OAI.UniversalTensorSquare.sg33317`, `OAI.UniversalTensorSquare.sg33325`, `OAI.UniversalTensorSquare.sg33330`, `OAI.UniversalTensorSquare.sg33332`, `OAI.UniversalTensorSquare.sg33345`, `OAI.UniversalTensorSquare.sg33359`, `OAI.UniversalTensorSquare.sg33368`, `OAI.UniversalTensorSquare.sg33369`, `OAI.UniversalTensorSquare.sg33371`, `OAI.UniversalTensorSquare.sg33374`, `OAI.UniversalTensorSquare.sg33377`, `OAI.UniversalTensorSquare.sg33386`, `OAI.UniversalTensorSquare.sg33397`, `OAI.UniversalTensorSquare.sg33399`, `OAI.UniversalTensorSquare.sg33401`, `OAI.UniversalTensorSquare.sg33402`, `OAI.UniversalTensorSquare.sg33406`, `OAI.UniversalTensorSquare.sg33408`, `OAI.UniversalTensorSquare.sg33415`, `OAI.UniversalTensorSquare.sg33416`, `OAI.UniversalTensorSquare.sg33429`, `OAI.UniversalTensorSquare.sg33430`, `OAI.UniversalTensorSquare.sg33434`, `OAI.UniversalTensorSquare.sg33436`, `OAI.UniversalTensorSquare.sg33439`, `OAI.UniversalTensorSquare.sg33441`, `OAI.UniversalTensorSquare.sg33452`, `OAI.UniversalTensorSquare.sg33455`, `OAI.UniversalTensorSquare.sg33457`, `OAI.UniversalTensorSquare.sg33460`, `OAI.UniversalTensorSquare.sg33461`, `OAI.UniversalTensorSquare.sg33462`, `OAI.UniversalTensorSquare.sg33465`, `OAI.UniversalTensorSquare.sg33470`, `OAI.UniversalTensorSquare.sg33472`, `OAI.UniversalTensorSquare.sg33474`, `OAI.UniversalTensorSquare.sg33492`, `OAI.UniversalTensorSquare.sg33495`, `OAI.UniversalTensorSquare.sg33518`, `OAI.UniversalTensorSquare.sg33526`, `OAI.UniversalTensorSquare.sg33527`, `OAI.UniversalTensorSquare.sg33536`, `OAI.UniversalTensorSquare.sg33540`, `OAI.UniversalTensorSquare.sg33545`, `OAI.UniversalTensorSquare.sg33553`, `OAI.UniversalTensorSquare.sg33558`, `OAI.UniversalTensorSquare.sg33566`, `OAI.UniversalTensorSquare.sg33568`, `OAI.UniversalTensorSquare.sg33580`, `OAI.UniversalTensorSquare.sg33584`, `OAI.UniversalTensorSquare.sg33588`, `OAI.UniversalTensorSquare.sg33589`, `OAI.UniversalTensorSquare.sg33590`, `OAI.UniversalTensorSquare.sg33591`, `OAI.UniversalTensorSquare.sg33592`, `OAI.UniversalTensorSquare.sg33595`, `OAI.UniversalTensorSquare.sg33603`, `OAI.UniversalTensorSquare.sg33604`, `OAI.UniversalTensorSquare.sg33605`, `OAI.UniversalTensorSquare.sg33606`, `OAI.UniversalTensorSquare.sg33608`, `OAI.UniversalTensorSquare.sg33609`, `OAI.UniversalTensorSquare.sg33610`, `OAI.UniversalTensorSquare.sg33611`, `OAI.UniversalTensorSquare.sg33612`, `OAI.UniversalTensorSquare.sg33613`, `OAI.UniversalTensorSquare.sg33615`, `OAI.UniversalTensorSquare.sg33627`, `OAI.UniversalTensorSquare.sg33628`, `OAI.UniversalTensorSquare.sg33632`, `OAI.UniversalTensorSquare.sg33634`, `OAI.UniversalTensorSquare.sg33635`, `OAI.UniversalTensorSquare.sg33639`, `OAI.UniversalTensorSquare.sg33641`, `OAI.UniversalTensorSquare.sg33642`, `OAI.UniversalTensorSquare.sg33644`, `OAI.UniversalTensorSquare.sg33645`, `OAI.UniversalTensorSquare.sg33646`, `OAI.UniversalTensorSquare.sg33649`, `OAI.UniversalTensorSquare.sg33655`, `OAI.UniversalTensorSquare.sg33661`, `OAI.UniversalTensorSquare.sg33662`, `OAI.UniversalTensorSquare.sg33663`, `OAI.UniversalTensorSquare.sg33666`, `OAI.UniversalTensorSquare.sg33678`, `OAI.UniversalTensorSquare.sg33686`, `OAI.UniversalTensorSquare.sg33690`, `OAI.UniversalTensorSquare.sg33692`, `OAI.UniversalTensorSquare.sg33701`, `OAI.UniversalTensorSquare.sg33704`, `OAI.UniversalTensorSquare.sg33706`, `OAI.UniversalTensorSquare.sg33714`, `OAI.UniversalTensorSquare.sg33722`, `OAI.UniversalTensorSquare.sg33727`, `OAI.UniversalTensorSquare.sg33741`, `OAI.UniversalTensorSquare.sg33743`, `OAI.UniversalTensorSquare.sg33748`, `OAI.UniversalTensorSquare.sg33756`, `OAI.UniversalTensorSquare.sg33757`, `OAI.UniversalTensorSquare.sg33758`, `OAI.UniversalTensorSquare.sg33759`, `OAI.UniversalTensorSquare.sg33761`, `OAI.UniversalTensorSquare.sg33763`, `OAI.UniversalTensorSquare.sg33764`, `OAI.UniversalTensorSquare.sg33766`, `OAI.UniversalTensorSquare.sg33768`, `OAI.UniversalTensorSquare.sg33769`, `OAI.UniversalTensorSquare.sg33772`, `OAI.UniversalTensorSquare.sg33774`, `OAI.UniversalTensorSquare.sg33775`, `OAI.UniversalTensorSquare.sg33776`, `OAI.UniversalTensorSquare.sg33777`, `OAI.UniversalTensorSquare.sg33786`, `OAI.UniversalTensorSquare.sg33794`, `OAI.UniversalTensorSquare.sg33795`, `OAI.UniversalTensorSquare.sg33796`, `OAI.UniversalTensorSquare.sg33799`, `OAI.UniversalTensorSquare.sg33803`, `OAI.UniversalTensorSquare.sg33818`, `OAI.UniversalTensorSquare.sg33820`, `OAI.UniversalTensorSquare.sg33821`, `OAI.UniversalTensorSquare.sg33831`, `OAI.UniversalTensorSquare.sg33832`, `OAI.UniversalTensorSquare.sg33833`, `OAI.UniversalTensorSquare.sg33835`, `OAI.UniversalTensorSquare.sg33836`, `OAI.UniversalTensorSquare.sg33838`, `OAI.UniversalTensorSquare.sg33839`, `OAI.UniversalTensorSquare.sg33843`, `OAI.UniversalTensorSquare.sg33847`, `OAI.UniversalTensorSquare.sg33848`, `OAI.UniversalTensorSquare.sg33849`, `OAI.UniversalTensorSquare.sg33855`, `OAI.UniversalTensorSquare.sg33857`, `OAI.UniversalTensorSquare.sg33859`, `OAI.UniversalTensorSquare.sg33863`, `OAI.UniversalTensorSquare.sg33864`, `OAI.UniversalTensorSquare.sg33865`, `OAI.UniversalTensorSquare.sg33868`, `OAI.UniversalTensorSquare.sg33872`, `OAI.UniversalTensorSquare.sg33873`, `OAI.UniversalTensorSquare.sg33874`, `OAI.UniversalTensorSquare.sg33876`, `OAI.UniversalTensorSquare.sg33877`, `OAI.UniversalTensorSquare.sg33879`, `OAI.UniversalTensorSquare.sg33880`, `OAI.UniversalTensorSquare.sg33882`, `OAI.UniversalTensorSquare.sg33887`, `OAI.UniversalTensorSquare.sg33893`, `OAI.UniversalTensorSquare.sg33895`, `OAI.UniversalTensorSquare.sg33896`, `OAI.UniversalTensorSquare.sg33898`, `OAI.UniversalTensorSquare.sg33900`, `OAI.UniversalTensorSquare.sg33902`, `OAI.UniversalTensorSquare.sg33904`, `OAI.UniversalTensorSquare.sg33908`, `OAI.UniversalTensorSquare.sg33909`, `OAI.UniversalTensorSquare.sg33913`, `OAI.UniversalTensorSquare.sg33917`, `OAI.UniversalTensorSquare.sg33919`, `OAI.UniversalTensorSquare.sg33921`, `OAI.UniversalTensorSquare.sg33923`, `OAI.UniversalTensorSquare.sg33924`, `OAI.UniversalTensorSquare.sg33925`, `OAI.UniversalTensorSquare.sg33933`, `OAI.UniversalTensorSquare.sg33934`, `OAI.UniversalTensorSquare.sg33935`, `OAI.UniversalTensorSquare.sg33938`, `OAI.UniversalTensorSquare.sg33939`, `OAI.UniversalTensorSquare.sg33940`, `OAI.UniversalTensorSquare.sg33945`, `OAI.UniversalTensorSquare.sg33953`, `OAI.UniversalTensorSquare.sg33954`, `OAI.UniversalTensorSquare.sg33966`, `OAI.UniversalTensorSquare.sg33969`, `OAI.UniversalTensorSquare.sg33971`, `OAI.UniversalTensorSquare.sg33972`, `OAI.UniversalTensorSquare.sg33973`, `OAI.UniversalTensorSquare.sg33975`, `OAI.UniversalTensorSquare.sg33979`, `OAI.UniversalTensorSquare.sg33994`, `OAI.UniversalTensorSquare.sg33995`, `OAI.UniversalTensorSquare.sg34003`, `OAI.UniversalTensorSquare.sg34012`, `OAI.UniversalTensorSquare.sg34013`, `OAI.UniversalTensorSquare.sg34020`, `OAI.UniversalTensorSquare.sg34033`, `OAI.UniversalTensorSquare.sg34035`, `OAI.UniversalTensorSquare.sg34036`, `OAI.UniversalTensorSquare.sg34038`, `OAI.UniversalTensorSquare.sg34039`, `OAI.UniversalTensorSquare.sg34046`, `OAI.UniversalTensorSquare.sg34049`, `OAI.UniversalTensorSquare.sg34051`, `OAI.UniversalTensorSquare.sg34052`, `OAI.UniversalTensorSquare.sg34055`, `OAI.UniversalTensorSquare.sg34062`, `OAI.UniversalTensorSquare.sg34084`, `OAI.UniversalTensorSquare.sg34085`, `OAI.UniversalTensorSquare.sg34089`, `OAI.UniversalTensorSquare.sg34092`, `OAI.UniversalTensorSquare.sg34093`, `OAI.UniversalTensorSquare.sg34095`, `OAI.UniversalTensorSquare.sg34096`, `OAI.UniversalTensorSquare.sg34105`, `OAI.UniversalTensorSquare.sg34112`, `OAI.UniversalTensorSquare.sg34115`, `OAI.UniversalTensorSquare.sg34117`, `OAI.UniversalTensorSquare.sg34122`, `OAI.UniversalTensorSquare.sg34126`, `OAI.UniversalTensorSquare.sg34127`, `OAI.UniversalTensorSquare.sg34128`, `OAI.UniversalTensorSquare.sg34130`, `OAI.UniversalTensorSquare.sg34132`, `OAI.UniversalTensorSquare.sg34139`, `OAI.UniversalTensorSquare.sg34140`, `OAI.UniversalTensorSquare.sg34142`, `OAI.UniversalTensorSquare.sg34148`, `OAI.UniversalTensorSquare.sg34153`, `OAI.UniversalTensorSquare.sg34156`, `OAI.UniversalTensorSquare.sg34158`, `OAI.UniversalTensorSquare.sg34164`, `OAI.UniversalTensorSquare.sg34166`, `OAI.UniversalTensorSquare.sg34170`, `OAI.UniversalTensorSquare.sg34171`, `OAI.UniversalTensorSquare.sg34172`, `OAI.UniversalTensorSquare.sg34174`, `OAI.UniversalTensorSquare.sg34179`, `OAI.UniversalTensorSquare.sg34190`, `OAI.UniversalTensorSquare.sg34193`, `OAI.UniversalTensorSquare.sg34194`, `OAI.UniversalTensorSquare.sg34195`, `OAI.UniversalTensorSquare.sg34196`, `OAI.UniversalTensorSquare.sg34203`, `OAI.UniversalTensorSquare.sg34208`, `OAI.UniversalTensorSquare.sg34219`, `OAI.UniversalTensorSquare.sg34239`, `OAI.UniversalTensorSquare.sg34241`, `OAI.UniversalTensorSquare.sg34245`, `OAI.UniversalTensorSquare.sg34263`, `OAI.UniversalTensorSquare.sg34284`, `OAI.UniversalTensorSquare.sg34289`, `OAI.UniversalTensorSquare.sg34290`, `OAI.UniversalTensorSquare.sg34291`, `OAI.UniversalTensorSquare.sg34293`, `OAI.UniversalTensorSquare.sg34294`, `OAI.UniversalTensorSquare.sg34296`, `OAI.UniversalTensorSquare.sg34297`, `OAI.UniversalTensorSquare.sg34298`, `OAI.UniversalTensorSquare.sg34310`, `OAI.UniversalTensorSquare.sg34311`, `OAI.UniversalTensorSquare.sg34312`, `OAI.UniversalTensorSquare.sg34314`, `OAI.UniversalTensorSquare.sg34315`, `OAI.UniversalTensorSquare.sg34317`, `OAI.UniversalTensorSquare.sg34318`, `OAI.UniversalTensorSquare.sg34325`, `OAI.UniversalTensorSquare.sg34326`, `OAI.UniversalTensorSquare.sg34329`, `OAI.UniversalTensorSquare.sg34333`, `OAI.UniversalTensorSquare.sg34336`, `OAI.UniversalTensorSquare.sg34340`, `OAI.UniversalTensorSquare.sg34342`, `OAI.UniversalTensorSquare.sg34348`, `OAI.UniversalTensorSquare.sg34357`, `OAI.UniversalTensorSquare.sg34362`, `OAI.UniversalTensorSquare.sg34364`, `OAI.UniversalTensorSquare.sg34366`, `OAI.UniversalTensorSquare.sg34368`, `OAI.UniversalTensorSquare.sg34383`, `OAI.UniversalTensorSquare.sg34386`, `OAI.UniversalTensorSquare.sg34393`, `OAI.UniversalTensorSquare.sg34395`, `OAI.UniversalTensorSquare.sg34399`, `OAI.UniversalTensorSquare.sg34415`, `OAI.UniversalTensorSquare.sg34416`, `OAI.UniversalTensorSquare.sg34417`, `OAI.UniversalTensorSquare.sg34420`, `OAI.UniversalTensorSquare.sg34425`, `OAI.UniversalTensorSquare.sg34427`, `OAI.UniversalTensorSquare.sg34429`, `OAI.UniversalTensorSquare.sg34431`, `OAI.UniversalTensorSquare.sg34445`, `OAI.UniversalTensorSquare.sg34450`, `OAI.UniversalTensorSquare.sg34458`, `OAI.UniversalTensorSquare.sg34460`, `OAI.UniversalTensorSquare.sg34464`, `OAI.UniversalTensorSquare.sg34467`, `OAI.UniversalTensorSquare.sg34471`, `OAI.UniversalTensorSquare.sg34472`, `OAI.UniversalTensorSquare.sg34473`, `OAI.UniversalTensorSquare.sg34474`, `OAI.UniversalTensorSquare.sg34475`, `OAI.UniversalTensorSquare.sg34476`, `OAI.UniversalTensorSquare.sg34477`, `OAI.UniversalTensorSquare.sg34479`, `OAI.UniversalTensorSquare.sg34480`, `OAI.UniversalTensorSquare.sg34483`, `OAI.UniversalTensorSquare.sg34485`, `OAI.UniversalTensorSquare.sg34487`, `OAI.UniversalTensorSquare.sg34494`, `OAI.UniversalTensorSquare.sg34498`, `OAI.UniversalTensorSquare.sg34503`, `OAI.UniversalTensorSquare.sg34508`, `OAI.UniversalTensorSquare.sg34510`, `OAI.UniversalTensorSquare.sg34512`, `OAI.UniversalTensorSquare.sg34514`, `OAI.UniversalTensorSquare.sg34515`, `OAI.UniversalTensorSquare.sg34518`, `OAI.UniversalTensorSquare.sg34521`, `OAI.UniversalTensorSquare.sg34525`, `OAI.UniversalTensorSquare.sg34527`, `OAI.UniversalTensorSquare.sg34530`, `OAI.UniversalTensorSquare.sg34533`, `OAI.UniversalTensorSquare.sg34535`, `OAI.UniversalTensorSquare.sg34537`, `OAI.UniversalTensorSquare.sg34539`, `OAI.UniversalTensorSquare.sg34540`, `OAI.UniversalTensorSquare.sg34559`, `OAI.UniversalTensorSquare.sg34561`, `OAI.UniversalTensorSquare.sg34562`, `OAI.UniversalTensorSquare.sg34573`, `OAI.UniversalTensorSquare.sg34579`, `OAI.UniversalTensorSquare.sg34582`, `OAI.UniversalTensorSquare.sg34583`, `OAI.UniversalTensorSquare.sg34588`, `OAI.UniversalTensorSquare.sg34589`, `OAI.UniversalTensorSquare.sg34595`, `OAI.UniversalTensorSquare.sg34596`, `OAI.UniversalTensorSquare.sg34603`, `OAI.UniversalTensorSquare.sg34604`, `OAI.UniversalTensorSquare.sg34607`, `OAI.UniversalTensorSquare.sg34609`, `OAI.UniversalTensorSquare.sg34610`, `OAI.UniversalTensorSquare.sg34642`, `OAI.UniversalTensorSquare.sg34644`, `OAI.UniversalTensorSquare.sg34646`, `OAI.UniversalTensorSquare.sg34675`, `OAI.UniversalTensorSquare.sg34693`, `OAI.UniversalTensorSquare.sg34698`, `OAI.UniversalTensorSquare.sg34701`, `OAI.UniversalTensorSquare.sg34706`, `OAI.UniversalTensorSquare.sg34708`, `OAI.UniversalTensorSquare.sg34709`, `OAI.UniversalTensorSquare.sg34731`, `OAI.UniversalTensorSquare.sg34734`, `OAI.UniversalTensorSquare.sg34736`, `OAI.UniversalTensorSquare.sg34746`, `OAI.UniversalTensorSquare.sg34750`, `OAI.UniversalTensorSquare.sg34752`, `OAI.UniversalTensorSquare.sg34770`, `OAI.UniversalTensorSquare.sg34787`, `OAI.UniversalTensorSquare.sg34792`, `OAI.UniversalTensorSquare.sg34795`, `OAI.UniversalTensorSquare.sg34797`, `OAI.UniversalTensorSquare.sg34807`, `OAI.UniversalTensorSquare.sg34824`, `OAI.UniversalTensorSquare.sg34836`, `OAI.UniversalTensorSquare.sg34841`, `OAI.UniversalTensorSquare.sg34864`, `OAI.UniversalTensorSquare.sg34880`, `OAI.UniversalTensorSquare.sg34882`, `OAI.UniversalTensorSquare.sg34886`, `OAI.UniversalTensorSquare.sg34888`, `OAI.UniversalTensorSquare.sg34892`, `OAI.UniversalTensorSquare.sg34895`, `OAI.UniversalTensorSquare.sg34896`, `OAI.UniversalTensorSquare.sg34897`, `OAI.UniversalTensorSquare.sg34898`, `OAI.UniversalTensorSquare.sg34901`, `OAI.UniversalTensorSquare.sg34904`, `OAI.UniversalTensorSquare.sg34914`, `OAI.UniversalTensorSquare.sg34916`, `OAI.UniversalTensorSquare.sg34946`, `OAI.UniversalTensorSquare.sg34952`, `OAI.UniversalTensorSquare.sg34959`, `OAI.UniversalTensorSquare.sg34962`, `OAI.UniversalTensorSquare.sg34964`, `OAI.UniversalTensorSquare.sg34975`, `OAI.UniversalTensorSquare.sg34980`, `OAI.UniversalTensorSquare.sg34983`, `OAI.UniversalTensorSquare.sg34985`, `OAI.UniversalTensorSquare.sg34993`, `OAI.UniversalTensorSquare.sg35003`, `OAI.UniversalTensorSquare.sg35005`, `OAI.UniversalTensorSquare.sg35011`, `OAI.UniversalTensorSquare.sg35013`, `OAI.UniversalTensorSquare.sg35020`, `OAI.UniversalTensorSquare.sg35033`, `OAI.UniversalTensorSquare.sg35037`, `OAI.UniversalTensorSquare.sg35039`, `OAI.UniversalTensorSquare.sg35041`, `OAI.UniversalTensorSquare.sg35045`, `OAI.UniversalTensorSquare.sg35047`, `OAI.UniversalTensorSquare.sg35051`, `OAI.UniversalTensorSquare.sg35058`, `OAI.UniversalTensorSquare.sg35082`, `OAI.UniversalTensorSquare.sg35085`, `OAI.UniversalTensorSquare.sg35086`, `OAI.UniversalTensorSquare.sg35104`, `OAI.UniversalTensorSquare.sg35113`, `OAI.UniversalTensorSquare.sg35116`, `OAI.UniversalTensorSquare.sg35123`, `OAI.UniversalTensorSquare.sg35130`, `OAI.UniversalTensorSquare.sg35151`, `OAI.UniversalTensorSquare.sg35156`, `OAI.UniversalTensorSquare.sg35164`, `OAI.UniversalTensorSquare.sg35181`, `OAI.UniversalTensorSquare.sg35183`, `OAI.UniversalTensorSquare.sg35209`, `OAI.UniversalTensorSquare.sg35227`, `OAI.UniversalTensorSquare.sg35235`, `OAI.UniversalTensorSquare.sg35256`, `OAI.UniversalTensorSquare.sg35270`, `OAI.UniversalTensorSquare.sg35275`, `OAI.UniversalTensorSquare.sg35276`, `OAI.UniversalTensorSquare.sg35278`, `OAI.UniversalTensorSquare.sg35280`, `OAI.UniversalTensorSquare.sg35288`, `OAI.UniversalTensorSquare.sg35294`, `OAI.UniversalTensorSquare.sg35298`, `OAI.UniversalTensorSquare.sg35303`, `OAI.UniversalTensorSquare.sg35316`, `OAI.UniversalTensorSquare.sg35323`, `OAI.UniversalTensorSquare.sg35325`, `OAI.UniversalTensorSquare.sg35326`, `OAI.UniversalTensorSquare.sg35330`, `OAI.UniversalTensorSquare.sg35332`, `OAI.UniversalTensorSquare.sg35336`, `OAI.UniversalTensorSquare.sg35362`, `OAI.UniversalTensorSquare.sg35365`, `OAI.UniversalTensorSquare.sg35371`, `OAI.UniversalTensorSquare.sg35373`, `OAI.UniversalTensorSquare.sg35376`, `OAI.UniversalTensorSquare.sg35377`, `OAI.UniversalTensorSquare.sg35378`, `OAI.UniversalTensorSquare.sg35382`, `OAI.UniversalTensorSquare.sg35384`, `OAI.UniversalTensorSquare.sg35390`, `OAI.UniversalTensorSquare.sg35391`, `OAI.UniversalTensorSquare.sg35392`, `OAI.UniversalTensorSquare.sg35396`, `OAI.UniversalTensorSquare.sg35397`, `OAI.UniversalTensorSquare.sg35399`, `OAI.UniversalTensorSquare.sg35400`, `OAI.UniversalTensorSquare.sg35402`, `OAI.UniversalTensorSquare.sg35403`, `OAI.UniversalTensorSquare.sg35404`, `OAI.UniversalTensorSquare.sg35417`, `OAI.UniversalTensorSquare.sg35423`, `OAI.UniversalTensorSquare.sg35428`, `OAI.UniversalTensorSquare.sg35429`, `OAI.UniversalTensorSquare.sg35434`, `OAI.UniversalTensorSquare.sg35446`, `OAI.UniversalTensorSquare.sg35456`, `OAI.UniversalTensorSquare.sg35458`, `OAI.UniversalTensorSquare.sg35460`, `OAI.UniversalTensorSquare.sg35462`, `OAI.UniversalTensorSquare.sg35464`, `OAI.UniversalTensorSquare.sg35465`, `OAI.UniversalTensorSquare.sg35466`, `OAI.UniversalTensorSquare.sg35467`, `OAI.UniversalTensorSquare.sg35469`, `OAI.UniversalTensorSquare.sg35481`, `OAI.UniversalTensorSquare.sg35501`, `OAI.UniversalTensorSquare.sg35507`, `OAI.UniversalTensorSquare.sg35508`, `OAI.UniversalTensorSquare.sg35509`, `OAI.UniversalTensorSquare.sg35585`, `OAI.UniversalTensorSquare.sg35589`, `OAI.UniversalTensorSquare.sg35590`, `OAI.UniversalTensorSquare.sg35597`, `OAI.UniversalTensorSquare.sg35599`, `OAI.UniversalTensorSquare.sg35601`, `OAI.UniversalTensorSquare.sg35610`, `OAI.UniversalTensorSquare.sg35632`, `OAI.UniversalTensorSquare.sg35634`, `OAI.UniversalTensorSquare.sg35635`, `OAI.UniversalTensorSquare.sg35636`, `OAI.UniversalTensorSquare.sg35644`, `OAI.UniversalTensorSquare.sg35675`, `OAI.UniversalTensorSquare.sg35766`, `OAI.UniversalTensorSquare.sg35786`, `OAI.UniversalTensorSquare.sg35801`, `OAI.UniversalTensorSquare.sg35808`, `OAI.UniversalTensorSquare.sg35811`, `OAI.UniversalTensorSquare.sg35813`, `OAI.UniversalTensorSquare.sg35835`, `OAI.UniversalTensorSquare.sg35836`, `OAI.UniversalTensorSquare.sg35933`, `OAI.UniversalTensorSquare.sg35951`, `OAI.UniversalTensorSquare.sg35959`, `OAI.UniversalTensorSquare.sg35972`, `OAI.UniversalTensorSquare.sg35983`, `OAI.UniversalTensorSquare.sg36073`, `OAI.UniversalTensorSquare.sg36084`, `OAI.UniversalTensorSquare.sg36088`, `OAI.UniversalTensorSquare.sg36099`, `OAI.UniversalTensorSquare.sg36103`, `OAI.UniversalTensorSquare.sg36104`, `OAI.UniversalTensorSquare.sg36109`, `OAI.UniversalTensorSquare.sg36116`, `OAI.UniversalTensorSquare.sg36122`, `OAI.UniversalTensorSquare.sg36124`, `OAI.UniversalTensorSquare.sg36126`, `OAI.UniversalTensorSquare.sg36127`, `OAI.UniversalTensorSquare.sg36145`, `OAI.UniversalTensorSquare.sg36146`, `OAI.UniversalTensorSquare.sg36174`, `OAI.UniversalTensorSquare.sg36176`, `OAI.UniversalTensorSquare.sg36178`, `OAI.UniversalTensorSquare.sg36181`, `OAI.UniversalTensorSquare.sg36209`, `OAI.UniversalTensorSquare.sg36210`, `OAI.UniversalTensorSquare.sg36218`, `OAI.UniversalTensorSquare.sg36220`, `OAI.UniversalTensorSquare.sg36234`, `OAI.UniversalTensorSquare.sg36281`, `OAI.UniversalTensorSquare.sg36286`, `OAI.UniversalTensorSquare.sg36287`, `OAI.UniversalTensorSquare.sg36289`, `OAI.UniversalTensorSquare.sg36290`, `OAI.UniversalTensorSquare.sg36292`, `OAI.UniversalTensorSquare.sg36293`, `OAI.UniversalTensorSquare.sg36294`, `OAI.UniversalTensorSquare.sg36296`, `OAI.UniversalTensorSquare.sg36297`, `OAI.UniversalTensorSquare.sg36300`, `OAI.UniversalTensorSquare.sg36302`, `OAI.UniversalTensorSquare.sg36303`, `OAI.UniversalTensorSquare.sg36318`, `OAI.UniversalTensorSquare.sg36340`, `OAI.UniversalTensorSquare.sg36400`, `OAI.UniversalTensorSquare.sg36406`, `OAI.UniversalTensorSquare.sg36449`, `OAI.UniversalTensorSquare.sg36452`, `OAI.UniversalTensorSquare.sg36454`, `OAI.UniversalTensorSquare.sg36461`, `OAI.UniversalTensorSquare.sg36463`, `OAI.UniversalTensorSquare.sg36468`, `OAI.UniversalTensorSquare.sg36519`, `OAI.UniversalTensorSquare.sg36525`, `OAI.UniversalTensorSquare.sg36529`, `OAI.UniversalTensorSquare.sg36530`, `OAI.UniversalTensorSquare.sg36534`, `OAI.UniversalTensorSquare.sg36535`, `OAI.UniversalTensorSquare.sg36537`, `OAI.UniversalTensorSquare.sg36540`, `OAI.UniversalTensorSquare.sg36544`, `OAI.UniversalTensorSquare.sg36566`, `OAI.UniversalTensorSquare.sg36581`, `OAI.UniversalTensorSquare.sg36584`, `OAI.UniversalTensorSquare.sg36588`, `OAI.UniversalTensorSquare.sg36590`, `OAI.UniversalTensorSquare.sg36592`, `OAI.UniversalTensorSquare.sg36604`, `OAI.UniversalTensorSquare.sg36612`, `OAI.UniversalTensorSquare.sg36620`, `OAI.UniversalTensorSquare.sg36667`, `OAI.UniversalTensorSquare.sg36690`, `OAI.UniversalTensorSquare.sg36691`, `OAI.UniversalTensorSquare.sg36704`, `OAI.UniversalTensorSquare.sg36723`, `OAI.UniversalTensorSquare.sg36749`, `OAI.UniversalTensorSquare.sg36773`, `OAI.UniversalTensorSquare.sg36775`, `OAI.UniversalTensorSquare.sg36779`, `OAI.UniversalTensorSquare.sg36782`, `OAI.UniversalTensorSquare.sg36784`, `OAI.UniversalTensorSquare.sg36801`, `OAI.UniversalTensorSquare.sg36804`, `OAI.UniversalTensorSquare.sg36807`, `OAI.UniversalTensorSquare.sg36811`, `OAI.UniversalTensorSquare.sg36812`, `OAI.UniversalTensorSquare.sg36814`, `OAI.UniversalTensorSquare.sg36819`, `OAI.UniversalTensorSquare.sg36839`, `OAI.UniversalTensorSquare.sg36864`, `OAI.UniversalTensorSquare.sg36867`, `OAI.UniversalTensorSquare.sg36869`, `OAI.UniversalTensorSquare.sg36877`, `OAI.UniversalTensorSquare.sg36886`, `OAI.UniversalTensorSquare.sg36889`, `OAI.UniversalTensorSquare.sg36891`, `OAI.UniversalTensorSquare.sg36921`, `OAI.UniversalTensorSquare.sg36963`, `OAI.UniversalTensorSquare.sg36972`, `OAI.UniversalTensorSquare.sg36980`, `OAI.UniversalTensorSquare.sg36981`, `OAI.UniversalTensorSquare.sg36993`, `OAI.UniversalTensorSquare.sg36995`, `OAI.UniversalTensorSquare.sg37019`, `OAI.UniversalTensorSquare.sg37020`, `OAI.UniversalTensorSquare.sg37023`, `OAI.UniversalTensorSquare.sg37027`, `OAI.UniversalTensorSquare.sg37029`, `OAI.UniversalTensorSquare.sg37031`, `OAI.UniversalTensorSquare.sg37033`, `OAI.UniversalTensorSquare.sg37034`, `OAI.UniversalTensorSquare.sg37040`, `OAI.UniversalTensorSquare.sg37041`, `OAI.UniversalTensorSquare.sg37042`, `OAI.UniversalTensorSquare.sg37044`, `OAI.UniversalTensorSquare.sg37051`, `OAI.UniversalTensorSquare.sg37053`, `OAI.UniversalTensorSquare.sg37055`, `OAI.UniversalTensorSquare.sg37057`, `OAI.UniversalTensorSquare.sg37093`, `OAI.UniversalTensorSquare.sg37152`, `OAI.UniversalTensorSquare.sg37258`, `OAI.UniversalTensorSquare.sg37261`, `OAI.UniversalTensorSquare.sg37263`, `OAI.UniversalTensorSquare.sg37280`, `OAI.UniversalTensorSquare.sg37289`, `OAI.UniversalTensorSquare.sg37294`, `OAI.UniversalTensorSquare.sg37311`, `OAI.UniversalTensorSquare.sg37325`, `OAI.UniversalTensorSquare.sg37331`, `OAI.UniversalTensorSquare.sg37384`, `OAI.UniversalTensorSquare.sg37398`, `OAI.UniversalTensorSquare.sg37400`, `OAI.UniversalTensorSquare.sg37402`, `OAI.UniversalTensorSquare.sg37414`, `OAI.UniversalTensorSquare.sg37421`, `OAI.UniversalTensorSquare.sg37424`, `OAI.UniversalTensorSquare.sg37426`, `OAI.UniversalTensorSquare.sg37436`, `OAI.UniversalTensorSquare.sg37439`, `OAI.UniversalTensorSquare.sg37441`, `OAI.UniversalTensorSquare.sg37443`, `OAI.UniversalTensorSquare.sg37451`, `OAI.UniversalTensorSquare.sg37471`, `OAI.UniversalTensorSquare.sg37474`, `OAI.UniversalTensorSquare.sg37476`, `OAI.UniversalTensorSquare.sg37484`, `OAI.UniversalTensorSquare.sg37486`, `OAI.UniversalTensorSquare.sg37549`, `OAI.UniversalTensorSquare.sg37552`, `OAI.UniversalTensorSquare.sg37555`, `OAI.UniversalTensorSquare.sg37559`, `OAI.UniversalTensorSquare.sg37561`, `OAI.UniversalTensorSquare.sg37578`, `OAI.UniversalTensorSquare.sg37581`, `OAI.UniversalTensorSquare.sg37583`, `OAI.UniversalTensorSquare.sg37588`, `OAI.UniversalTensorSquare.sg37590`, `OAI.UniversalTensorSquare.sg37596`, `OAI.UniversalTensorSquare.sg37600`, `OAI.UniversalTensorSquare.sg37608`, `OAI.UniversalTensorSquare.sg37620`, `OAI.UniversalTensorSquare.sg37621`, `OAI.UniversalTensorSquare.sg37622`, `OAI.UniversalTensorSquare.sg37624`, `OAI.UniversalTensorSquare.sg37625`, `OAI.UniversalTensorSquare.sg37627`, `OAI.UniversalTensorSquare.sg37628`, `OAI.UniversalTensorSquare.sg37630`, `OAI.UniversalTensorSquare.sg37635`, `OAI.UniversalTensorSquare.sg37637`, `OAI.UniversalTensorSquare.sg37643`, `OAI.UniversalTensorSquare.sg37664`, `OAI.UniversalTensorSquare.sg37669`, `OAI.UniversalTensorSquare.sg37671`, `OAI.UniversalTensorSquare.sg37673`, `OAI.UniversalTensorSquare.sg37678`, `OAI.UniversalTensorSquare.sg37691`, `OAI.UniversalTensorSquare.sg37702`, `OAI.UniversalTensorSquare.sg37704`, `OAI.UniversalTensorSquare.sg37711`, `OAI.UniversalTensorSquare.sg37748`, `OAI.UniversalTensorSquare.sg37821`, `OAI.UniversalTensorSquare.sg37822`, `OAI.UniversalTensorSquare.sg37824`, `OAI.UniversalTensorSquare.sg37826`, `OAI.UniversalTensorSquare.sg37841`, `OAI.UniversalTensorSquare.sg37860`, `OAI.UniversalTensorSquare.sg37909`, `OAI.UniversalTensorSquare.sg37914`, `OAI.UniversalTensorSquare.sg37917`, `OAI.UniversalTensorSquare.sg37919`, `OAI.UniversalTensorSquare.sg37943`, `OAI.UniversalTensorSquare.sg37946`, `OAI.UniversalTensorSquare.sg37950`, `OAI.UniversalTensorSquare.sg37958`, `OAI.UniversalTensorSquare.sg37959`, `OAI.UniversalTensorSquare.sg37973`, `OAI.UniversalTensorSquare.sg38024`, `OAI.UniversalTensorSquare.sg38038`, `OAI.UniversalTensorSquare.sg38044`, `OAI.UniversalTensorSquare.sg38048`, `OAI.UniversalTensorSquare.sg38052`, `OAI.UniversalTensorSquare.sg38056`, `OAI.UniversalTensorSquare.sg38059`, `OAI.UniversalTensorSquare.sg38065`, `OAI.UniversalTensorSquare.sg38092`, `OAI.UniversalTensorSquare.sg38095`, `OAI.UniversalTensorSquare.sg38097`, `OAI.UniversalTensorSquare.sg38118`, `OAI.UniversalTensorSquare.sg38119`, `OAI.UniversalTensorSquare.sg38120`, `OAI.UniversalTensorSquare.sg38122`, `OAI.UniversalTensorSquare.sg38123`, `OAI.UniversalTensorSquare.sg38125`, `OAI.UniversalTensorSquare.sg38126`, `OAI.UniversalTensorSquare.sg38130`, `OAI.UniversalTensorSquare.sg38132`, `OAI.UniversalTensorSquare.sg38149`, `OAI.UniversalTensorSquare.sg38152`, `OAI.UniversalTensorSquare.sg38154`, `OAI.UniversalTensorSquare.sg38172`, `OAI.UniversalTensorSquare.sg38174`, `OAI.UniversalTensorSquare.sg38177`, `OAI.UniversalTensorSquare.sg38183`, `OAI.UniversalTensorSquare.sg38184`, `OAI.UniversalTensorSquare.sg38188`, `OAI.UniversalTensorSquare.sg38190`, `OAI.UniversalTensorSquare.sg38191`, `OAI.UniversalTensorSquare.sg38193`, `OAI.UniversalTensorSquare.sg38199`, `OAI.UniversalTensorSquare.sg38200`, `OAI.UniversalTensorSquare.sg38228`, `OAI.UniversalTensorSquare.sg38265`, `OAI.UniversalTensorSquare.sg38267`, `OAI.UniversalTensorSquare.sg38277`, `OAI.UniversalTensorSquare.sg38279`, `OAI.UniversalTensorSquare.sg38281`, `OAI.UniversalTensorSquare.sg38285`, `OAI.UniversalTensorSquare.sg38293`, `OAI.UniversalTensorSquare.sg38298`, `OAI.UniversalTensorSquare.sg38301`, `OAI.UniversalTensorSquare.sg38303`, `OAI.UniversalTensorSquare.sg38308`, `OAI.UniversalTensorSquare.sg38317`, `OAI.UniversalTensorSquare.sg38321`, `OAI.UniversalTensorSquare.sg38341`, `OAI.UniversalTensorSquare.sg38342`, `OAI.UniversalTensorSquare.sg38345`, `OAI.UniversalTensorSquare.sg38346`, `OAI.UniversalTensorSquare.sg38348`, `OAI.UniversalTensorSquare.sg38349`, `OAI.UniversalTensorSquare.sg38356`, `OAI.UniversalTensorSquare.sg38360`, `OAI.UniversalTensorSquare.sg38361`, `OAI.UniversalTensorSquare.sg38363`, `OAI.UniversalTensorSquare.sg38364`, `OAI.UniversalTensorSquare.sg38366`, `OAI.UniversalTensorSquare.sg38368`, `OAI.UniversalTensorSquare.sg38379`, `OAI.UniversalTensorSquare.sg38392`, `OAI.UniversalTensorSquare.sg38395`, `OAI.UniversalTensorSquare.sg38397`, `OAI.UniversalTensorSquare.sg38405`, `OAI.UniversalTensorSquare.sg38413`, `OAI.UniversalTensorSquare.sg38416`, `OAI.UniversalTensorSquare.sg38418`, `OAI.UniversalTensorSquare.sg38450`, `OAI.UniversalTensorSquare.sg38469`, `OAI.UniversalTensorSquare.sg38472`, `OAI.UniversalTensorSquare.sg38474`, `OAI.UniversalTensorSquare.sg38477`, `OAI.UniversalTensorSquare.sg38485`, `OAI.UniversalTensorSquare.sg38488`, `OAI.UniversalTensorSquare.sg38518`, `OAI.UniversalTensorSquare.sg38521`, `OAI.UniversalTensorSquare.sg38523`, `OAI.UniversalTensorSquare.sg38536`, `OAI.UniversalTensorSquare.sg38550`, `OAI.UniversalTensorSquare.sg38576`, `OAI.UniversalTensorSquare.sg38580`, `OAI.UniversalTensorSquare.sg38591`, `OAI.UniversalTensorSquare.sg38593`, `OAI.UniversalTensorSquare.sg38594`, `OAI.UniversalTensorSquare.sg38596`, `OAI.UniversalTensorSquare.sg38599`, `OAI.UniversalTensorSquare.sg38601`, `OAI.UniversalTensorSquare.sg38612`, `OAI.UniversalTensorSquare.sg38617`, `OAI.UniversalTensorSquare.sg38649`, `OAI.UniversalTensorSquare.sg38661`, `OAI.UniversalTensorSquare.sg38684`, `OAI.UniversalTensorSquare.sg38686`, `OAI.UniversalTensorSquare.sg38688`, `OAI.UniversalTensorSquare.sg38690`, `OAI.UniversalTensorSquare.sg38693`, `OAI.UniversalTensorSquare.sg38695`, `OAI.UniversalTensorSquare.sg38696`, `OAI.UniversalTensorSquare.sg38698`, `OAI.UniversalTensorSquare.sg38707`, `OAI.UniversalTensorSquare.sg38710`, `OAI.UniversalTensorSquare.sg38712`, `OAI.UniversalTensorSquare.sg38721`, `OAI.UniversalTensorSquare.sg38724`, `OAI.UniversalTensorSquare.sg38726`, `OAI.UniversalTensorSquare.sg38727`, `OAI.UniversalTensorSquare.sg38729`, `OAI.UniversalTensorSquare.sg38731`, `OAI.UniversalTensorSquare.sg38749`, `OAI.UniversalTensorSquare.sg38751`, `OAI.UniversalTensorSquare.sg38752`, `OAI.UniversalTensorSquare.sg38753`, `OAI.UniversalTensorSquare.sg38754`, `OAI.UniversalTensorSquare.sg38756`, `OAI.UniversalTensorSquare.sg38758`, `OAI.UniversalTensorSquare.sg38759`, `OAI.UniversalTensorSquare.sg38760`, `OAI.UniversalTensorSquare.sg38762`, `OAI.UniversalTensorSquare.sg38763`, `OAI.UniversalTensorSquare.sg38768`, `OAI.UniversalTensorSquare.sg38808`, `OAI.UniversalTensorSquare.sg38815`, `OAI.UniversalTensorSquare.sg38839`, `OAI.UniversalTensorSquare.sg38846`, `OAI.UniversalTensorSquare.sg38847`, `OAI.UniversalTensorSquare.sg38848`, `OAI.UniversalTensorSquare.sg38849`, `OAI.UniversalTensorSquare.sg38851`, `OAI.UniversalTensorSquare.sg38856`, `OAI.UniversalTensorSquare.sg38858`, `OAI.UniversalTensorSquare.sg38866`, `OAI.UniversalTensorSquare.sg38871`, `OAI.UniversalTensorSquare.sg38873`, `OAI.UniversalTensorSquare.sg38879`, `OAI.UniversalTensorSquare.sg38898`, `OAI.UniversalTensorSquare.sg38902`, `OAI.UniversalTensorSquare.sg38906`, `OAI.UniversalTensorSquare.sg38909`, `OAI.UniversalTensorSquare.sg38911`, `OAI.UniversalTensorSquare.sg38918`, `OAI.UniversalTensorSquare.sg38919`, `OAI.UniversalTensorSquare.sg38930`, `OAI.UniversalTensorSquare.sg38952`, `OAI.UniversalTensorSquare.sg38967`, `OAI.UniversalTensorSquare.sg38970`, `OAI.UniversalTensorSquare.sg38972`, `OAI.UniversalTensorSquare.sg39024`, `OAI.UniversalTensorSquare.sg39027`, `OAI.UniversalTensorSquare.sg39029`, `OAI.UniversalTensorSquare.sg39042`, `OAI.UniversalTensorSquare.sg39044`, `OAI.UniversalTensorSquare.sg39046`, `OAI.UniversalTensorSquare.sg39048`, `OAI.UniversalTensorSquare.sg39052`, `OAI.UniversalTensorSquare.sg39059`, `OAI.UniversalTensorSquare.sg39061`, `OAI.UniversalTensorSquare.sg39063`, `OAI.UniversalTensorSquare.sg39070`, `OAI.UniversalTensorSquare.sg39072`, `OAI.UniversalTensorSquare.sg39083`, `OAI.UniversalTensorSquare.sg39086`, `OAI.UniversalTensorSquare.sg39088`, `OAI.UniversalTensorSquare.sg39107`, `OAI.UniversalTensorSquare.sg39110`, `OAI.UniversalTensorSquare.sg39112`, `OAI.UniversalTensorSquare.sg39119`, `OAI.UniversalTensorSquare.sg39143`, `OAI.UniversalTensorSquare.sg39144`, `OAI.UniversalTensorSquare.sg39147`, `OAI.UniversalTensorSquare.sg39174`, `OAI.UniversalTensorSquare.sg39210`, `OAI.UniversalTensorSquare.sg39213`, `OAI.UniversalTensorSquare.sg39215`, `OAI.UniversalTensorSquare.sg39237`, `OAI.UniversalTensorSquare.sg39239`, `OAI.UniversalTensorSquare.sg39241`, `OAI.UniversalTensorSquare.sg39256`, `OAI.UniversalTensorSquare.sg39274`, `OAI.UniversalTensorSquare.sg39277`, `OAI.UniversalTensorSquare.sg39282`, `OAI.UniversalTensorSquare.sg39285`, `OAI.UniversalTensorSquare.sg39289`, `OAI.UniversalTensorSquare.sg39304`, `OAI.UniversalTensorSquare.sg39307`, `OAI.UniversalTensorSquare.sg39308`, `OAI.UniversalTensorSquare.sg39314`, `OAI.UniversalTensorSquare.sg39317`, `OAI.UniversalTensorSquare.sg39318`, `OAI.UniversalTensorSquare.sg39321`, `OAI.UniversalTensorSquare.sg39332`, `OAI.UniversalTensorSquare.sg39345`, `OAI.UniversalTensorSquare.sg39347`, `OAI.UniversalTensorSquare.sg39351`, `OAI.UniversalTensorSquare.sg39354`, `OAI.UniversalTensorSquare.sg39355`, `OAI.UniversalTensorSquare.sg39357`, `OAI.UniversalTensorSquare.sg39382`, `OAI.UniversalTensorSquare.sg39390`, `OAI.UniversalTensorSquare.sg39395`, `OAI.UniversalTensorSquare.sg39397`, `OAI.UniversalTensorSquare.sg39413`, `OAI.UniversalTensorSquare.sg39421`, `OAI.UniversalTensorSquare.sg39422`, `OAI.UniversalTensorSquare.sg39424`, `OAI.UniversalTensorSquare.sg39437`, `OAI.UniversalTensorSquare.sg39442`, `OAI.UniversalTensorSquare.sg39445`, `OAI.UniversalTensorSquare.sg39446`, `OAI.UniversalTensorSquare.sg39456`, `OAI.UniversalTensorSquare.sg39457`, `OAI.UniversalTensorSquare.sg39471`, `OAI.UniversalTensorSquare.sg39477`, `OAI.UniversalTensorSquare.sg39480`, `OAI.UniversalTensorSquare.sg39481`, `OAI.UniversalTensorSquare.sg39483`, `OAI.UniversalTensorSquare.sg39487`, `OAI.UniversalTensorSquare.sg39493`, `OAI.UniversalTensorSquare.sg39494`, `OAI.UniversalTensorSquare.sg39503`, `OAI.UniversalTensorSquare.sg39511`, `OAI.UniversalTensorSquare.sg39515`, `OAI.UniversalTensorSquare.sg39518`, `OAI.UniversalTensorSquare.sg39519`, `OAI.UniversalTensorSquare.sg39524`, `OAI.UniversalTensorSquare.sg39548`, `OAI.UniversalTensorSquare.sg39551`, `OAI.UniversalTensorSquare.sg39552`, `OAI.UniversalTensorSquare.sg39578`, `OAI.UniversalTensorSquare.sg39580`, `OAI.UniversalTensorSquare.sg39581`, `OAI.UniversalTensorSquare.sg39587`, `OAI.UniversalTensorSquare.sg39661`, `OAI.UniversalTensorSquare.sg39664`, `OAI.UniversalTensorSquare.sg39665`, `OAI.UniversalTensorSquare.sg39698`, `OAI.UniversalTensorSquare.sg3972`, `OAI.UniversalTensorSquare.sg39728`, `OAI.UniversalTensorSquare.sg39741`, `OAI.UniversalTensorSquare.sg39755`, `OAI.UniversalTensorSquare.sg39776`, `OAI.UniversalTensorSquare.sg39779`, `OAI.UniversalTensorSquare.sg39790`, `OAI.UniversalTensorSquare.sg39812`, `OAI.UniversalTensorSquare.sg39837`, `OAI.UniversalTensorSquare.sg39838`, `OAI.UniversalTensorSquare.sg39862`, `OAI.UniversalTensorSquare.sg39869`, `OAI.UniversalTensorSquare.sg39870`, `OAI.UniversalTensorSquare.sg39872`, `OAI.UniversalTensorSquare.sg39880`, `OAI.UniversalTensorSquare.sg39886`, `OAI.UniversalTensorSquare.sg39887`, `OAI.UniversalTensorSquare.sg39888`, `OAI.UniversalTensorSquare.sg39890`, `OAI.UniversalTensorSquare.sg39891`, `OAI.UniversalTensorSquare.sg39892`, `OAI.UniversalTensorSquare.sg39895`, `OAI.UniversalTensorSquare.sg39902`, `OAI.UniversalTensorSquare.sg39903`, `OAI.UniversalTensorSquare.sg39905`, `OAI.UniversalTensorSquare.sg39907`, `OAI.UniversalTensorSquare.sg39909`, `OAI.UniversalTensorSquare.sg39912`, `OAI.UniversalTensorSquare.sg39913`, `OAI.UniversalTensorSquare.sg39919`, `OAI.UniversalTensorSquare.sg39936`, `OAI.UniversalTensorSquare.sg39937`, `OAI.UniversalTensorSquare.sg39942`, `OAI.UniversalTensorSquare.sg39954`, `OAI.UniversalTensorSquare.sg39959`, `OAI.UniversalTensorSquare.sg39970`, `OAI.UniversalTensorSquare.sg39971`, `OAI.UniversalTensorSquare.sg39972`, `OAI.UniversalTensorSquare.sg39974`, `OAI.UniversalTensorSquare.sg39981`, `OAI.UniversalTensorSquare.sg39983`, `OAI.UniversalTensorSquare.sg39984`, `OAI.UniversalTensorSquare.sg40021`, `OAI.UniversalTensorSquare.sg40027`, `OAI.UniversalTensorSquare.sg40029`, `OAI.UniversalTensorSquare.sg40030`, `OAI.UniversalTensorSquare.sg40039`, `OAI.UniversalTensorSquare.sg40046`, `OAI.UniversalTensorSquare.sg40049`, `OAI.UniversalTensorSquare.sg40061`, `OAI.UniversalTensorSquare.sg40063`, `OAI.UniversalTensorSquare.sg40064`, `OAI.UniversalTensorSquare.sg40076`, `OAI.UniversalTensorSquare.sg40078`, `OAI.UniversalTensorSquare.sg40079`, `OAI.UniversalTensorSquare.sg40097`, `OAI.UniversalTensorSquare.sg40099`, `OAI.UniversalTensorSquare.sg40100`, `OAI.UniversalTensorSquare.sg40127`, `OAI.UniversalTensorSquare.sg40131`, `OAI.UniversalTensorSquare.sg40133`, `OAI.UniversalTensorSquare.sg40134`, `OAI.UniversalTensorSquare.sg40136`, `OAI.UniversalTensorSquare.sg40138`, `OAI.UniversalTensorSquare.sg40165`, `OAI.UniversalTensorSquare.sg40167`, `OAI.UniversalTensorSquare.sg40168`, `OAI.UniversalTensorSquare.sg40170`, `OAI.UniversalTensorSquare.sg40174`, `OAI.UniversalTensorSquare.sg40177`, `OAI.UniversalTensorSquare.sg40180`, `OAI.UniversalTensorSquare.sg40181`, `OAI.UniversalTensorSquare.sg40183`, `OAI.UniversalTensorSquare.sg40197`, `OAI.UniversalTensorSquare.sg40198`, `OAI.UniversalTensorSquare.sg40199`, `OAI.UniversalTensorSquare.sg40200`, `OAI.UniversalTensorSquare.sg40201`, `OAI.UniversalTensorSquare.sg40202`, `OAI.UniversalTensorSquare.sg40205`, `OAI.UniversalTensorSquare.sg40212`, `OAI.UniversalTensorSquare.sg4022`, `OAI.UniversalTensorSquare.sg40221`, `OAI.UniversalTensorSquare.sg40241`, `OAI.UniversalTensorSquare.sg40244`, `OAI.UniversalTensorSquare.sg40245`, `OAI.UniversalTensorSquare.sg40256`, `OAI.UniversalTensorSquare.sg40313`, `OAI.UniversalTensorSquare.sg40356`, `OAI.UniversalTensorSquare.sg40357`, `OAI.UniversalTensorSquare.sg40368`, `OAI.UniversalTensorSquare.sg40381`, `OAI.UniversalTensorSquare.sg40422`, `OAI.UniversalTensorSquare.sg40450`, `OAI.UniversalTensorSquare.sg40482`, `OAI.UniversalTensorSquare.sg40484`, `OAI.UniversalTensorSquare.sg40485`, `OAI.UniversalTensorSquare.sg40517`, `OAI.UniversalTensorSquare.sg40521`, `OAI.UniversalTensorSquare.sg40553`, `OAI.UniversalTensorSquare.sg40562`, `OAI.UniversalTensorSquare.sg40563`, `OAI.UniversalTensorSquare.sg40565`, `OAI.UniversalTensorSquare.sg40571`, `OAI.UniversalTensorSquare.sg4058`, `OAI.UniversalTensorSquare.sg40582`, `OAI.UniversalTensorSquare.sg40607`, `OAI.UniversalTensorSquare.sg40613`, `OAI.UniversalTensorSquare.sg40614`, `OAI.UniversalTensorSquare.sg40616`, `OAI.UniversalTensorSquare.sg40619`, `OAI.UniversalTensorSquare.sg40622`, `OAI.UniversalTensorSquare.sg40623`, `OAI.UniversalTensorSquare.sg40628`, `OAI.UniversalTensorSquare.sg40630`, `OAI.UniversalTensorSquare.sg40631`, `OAI.UniversalTensorSquare.sg40632`, `OAI.UniversalTensorSquare.sg40633`, `OAI.UniversalTensorSquare.sg40634`, `OAI.UniversalTensorSquare.sg40640`, `OAI.UniversalTensorSquare.sg40643`, `OAI.UniversalTensorSquare.sg40657`, `OAI.UniversalTensorSquare.sg40659`, `OAI.UniversalTensorSquare.sg40660`, `OAI.UniversalTensorSquare.sg40664`, `OAI.UniversalTensorSquare.sg40666`, `OAI.UniversalTensorSquare.sg40667`, `OAI.UniversalTensorSquare.sg40676`, `OAI.UniversalTensorSquare.sg40678`, `OAI.UniversalTensorSquare.sg40679`, `OAI.UniversalTensorSquare.sg40681`, `OAI.UniversalTensorSquare.sg40682`, `OAI.UniversalTensorSquare.sg40704`, `OAI.UniversalTensorSquare.sg40710`, `OAI.UniversalTensorSquare.sg40713`, `OAI.UniversalTensorSquare.sg40714`, `OAI.UniversalTensorSquare.sg40716`, `OAI.UniversalTensorSquare.sg40724`, `OAI.UniversalTensorSquare.sg40726`, `OAI.UniversalTensorSquare.sg40727`, `OAI.UniversalTensorSquare.sg40738`, `OAI.UniversalTensorSquare.sg40748`, `OAI.UniversalTensorSquare.sg40751`, `OAI.UniversalTensorSquare.sg40754`, `OAI.UniversalTensorSquare.sg40758`, `OAI.UniversalTensorSquare.sg40760`, `OAI.UniversalTensorSquare.sg40761`, `OAI.UniversalTensorSquare.sg40763`, `OAI.UniversalTensorSquare.sg40769`, `OAI.UniversalTensorSquare.sg40770`, `OAI.UniversalTensorSquare.sg40783`, `OAI.UniversalTensorSquare.sg40785`, `OAI.UniversalTensorSquare.sg40791`, `OAI.UniversalTensorSquare.sg40794`, `OAI.UniversalTensorSquare.sg40795`, `OAI.UniversalTensorSquare.sg40808`, `OAI.UniversalTensorSquare.sg40812`, `OAI.UniversalTensorSquare.sg40814`, `OAI.UniversalTensorSquare.sg40815`, `OAI.UniversalTensorSquare.sg40841`, `OAI.UniversalTensorSquare.sg40850`, `OAI.UniversalTensorSquare.sg40861`, `OAI.UniversalTensorSquare.sg40879`, `OAI.UniversalTensorSquare.sg40897`, `OAI.UniversalTensorSquare.sg40898`, `OAI.UniversalTensorSquare.sg40899`, `OAI.UniversalTensorSquare.sg40908`, `OAI.UniversalTensorSquare.sg40910`, `OAI.UniversalTensorSquare.sg40911`, `OAI.UniversalTensorSquare.sg40916`, `OAI.UniversalTensorSquare.sg40917`, `OAI.UniversalTensorSquare.sg40918`, `OAI.UniversalTensorSquare.sg40930`, `OAI.UniversalTensorSquare.sg40942`, `OAI.UniversalTensorSquare.sg40959`, `OAI.UniversalTensorSquare.sg40985`, `OAI.UniversalTensorSquare.sg40986`, `OAI.UniversalTensorSquare.sg40992`, `OAI.UniversalTensorSquare.sg40999`, `OAI.UniversalTensorSquare.sg41005`, `OAI.UniversalTensorSquare.sg41007`, `OAI.UniversalTensorSquare.sg41021`, `OAI.UniversalTensorSquare.sg41024`, `OAI.UniversalTensorSquare.sg41025`, `OAI.UniversalTensorSquare.sg41026`, `OAI.UniversalTensorSquare.sg41031`, `OAI.UniversalTensorSquare.sg41032`, `OAI.UniversalTensorSquare.sg41034`, `OAI.UniversalTensorSquare.sg41052`, `OAI.UniversalTensorSquare.sg41054`, `OAI.UniversalTensorSquare.sg41055`, `OAI.UniversalTensorSquare.sg41059`, `OAI.UniversalTensorSquare.sg41060`, `OAI.UniversalTensorSquare.sg41062`, `OAI.UniversalTensorSquare.sg41068`, `OAI.UniversalTensorSquare.sg41077`, `OAI.UniversalTensorSquare.sg41078`, `OAI.UniversalTensorSquare.sg41094`, `OAI.UniversalTensorSquare.sg41095`, `OAI.UniversalTensorSquare.sg41105`, `OAI.UniversalTensorSquare.sg41106`, `OAI.UniversalTensorSquare.sg41114`, `OAI.UniversalTensorSquare.sg41116`, `OAI.UniversalTensorSquare.sg41130`, `OAI.UniversalTensorSquare.sg41139`, `OAI.UniversalTensorSquare.sg41141`, `OAI.UniversalTensorSquare.sg41142`, `OAI.UniversalTensorSquare.sg41143`, `OAI.UniversalTensorSquare.sg41144`, `OAI.UniversalTensorSquare.sg41145`, `OAI.UniversalTensorSquare.sg41146`, `OAI.UniversalTensorSquare.sg41153`, `OAI.UniversalTensorSquare.sg41154`, `OAI.UniversalTensorSquare.sg41155`, `OAI.UniversalTensorSquare.sg41168`, `OAI.UniversalTensorSquare.sg41170`, `OAI.UniversalTensorSquare.sg41171`, `OAI.UniversalTensorSquare.sg41175`, `OAI.UniversalTensorSquare.sg41177`, `OAI.UniversalTensorSquare.sg41178`, `OAI.UniversalTensorSquare.sg41179`, `OAI.UniversalTensorSquare.sg41180`, `OAI.UniversalTensorSquare.sg41195`, `OAI.UniversalTensorSquare.sg41197`, `OAI.UniversalTensorSquare.sg41203`, `OAI.UniversalTensorSquare.sg41209`, `OAI.UniversalTensorSquare.sg41211`, `OAI.UniversalTensorSquare.sg41212`, `OAI.UniversalTensorSquare.sg41224`, `OAI.UniversalTensorSquare.sg41226`, `OAI.UniversalTensorSquare.sg41245`, `OAI.UniversalTensorSquare.sg41256`, `OAI.UniversalTensorSquare.sg41258`, `OAI.UniversalTensorSquare.sg41267`, `OAI.UniversalTensorSquare.sg41277`, `OAI.UniversalTensorSquare.sg41278`, `OAI.UniversalTensorSquare.sg41280`, `OAI.UniversalTensorSquare.sg41301`, `OAI.UniversalTensorSquare.sg41302`, `OAI.UniversalTensorSquare.sg41336`, `OAI.UniversalTensorSquare.sg41346`, `OAI.UniversalTensorSquare.sg41347`, `OAI.UniversalTensorSquare.sg41359`, `OAI.UniversalTensorSquare.sg41363`, `OAI.UniversalTensorSquare.sg41375`, `OAI.UniversalTensorSquare.sg41385`, `OAI.UniversalTensorSquare.sg41386`, `OAI.UniversalTensorSquare.sg41388`, `OAI.UniversalTensorSquare.sg41394`, `OAI.UniversalTensorSquare.sg41397`, `OAI.UniversalTensorSquare.sg41409`, `OAI.UniversalTensorSquare.sg41413`, `OAI.UniversalTensorSquare.sg41439`, `OAI.UniversalTensorSquare.sg41440`, `OAI.UniversalTensorSquare.sg41442`, `OAI.UniversalTensorSquare.sg41451`, `OAI.UniversalTensorSquare.sg41457`, `OAI.UniversalTensorSquare.sg41460`, `OAI.UniversalTensorSquare.sg41466`, `OAI.UniversalTensorSquare.sg41480`, `OAI.UniversalTensorSquare.sg41482`, `OAI.UniversalTensorSquare.sg41490`, `OAI.UniversalTensorSquare.sg41492`, `OAI.UniversalTensorSquare.sg41496`, `OAI.UniversalTensorSquare.sg41499`, `OAI.UniversalTensorSquare.sg41503`, `OAI.UniversalTensorSquare.sg41524`, `OAI.UniversalTensorSquare.sg41533`, `OAI.UniversalTensorSquare.sg41535`, `OAI.UniversalTensorSquare.sg41552`, `OAI.UniversalTensorSquare.sg41560`, `OAI.UniversalTensorSquare.sg41574`, `OAI.UniversalTensorSquare.sg41575`, `OAI.UniversalTensorSquare.sg41601`, `OAI.UniversalTensorSquare.sg41625`, `OAI.UniversalTensorSquare.sg41627`, `OAI.UniversalTensorSquare.sg41641`, `OAI.UniversalTensorSquare.sg41645`, `OAI.UniversalTensorSquare.sg41662`, `OAI.UniversalTensorSquare.sg41680`, `OAI.UniversalTensorSquare.sg41714`, `OAI.UniversalTensorSquare.sg41717`, `OAI.UniversalTensorSquare.sg41718`, `OAI.UniversalTensorSquare.sg41720`, `OAI.UniversalTensorSquare.sg41725`, `OAI.UniversalTensorSquare.sg41729`, `OAI.UniversalTensorSquare.sg41755`, `OAI.UniversalTensorSquare.sg41769`, `OAI.UniversalTensorSquare.sg41775`, `OAI.UniversalTensorSquare.sg41794`, `OAI.UniversalTensorSquare.sg41807`, `OAI.UniversalTensorSquare.sg41808`, `OAI.UniversalTensorSquare.sg41816`, `OAI.UniversalTensorSquare.sg41817`, `OAI.UniversalTensorSquare.sg41819`, `OAI.UniversalTensorSquare.sg41823`, `OAI.UniversalTensorSquare.sg41824`, `OAI.UniversalTensorSquare.sg41826`, `OAI.UniversalTensorSquare.sg41834`, `OAI.UniversalTensorSquare.sg41837`, `OAI.UniversalTensorSquare.sg41838`, `OAI.UniversalTensorSquare.sg41859`, `OAI.UniversalTensorSquare.sg41863`, `OAI.UniversalTensorSquare.sg41868`, `OAI.UniversalTensorSquare.sg41889`, `OAI.UniversalTensorSquare.sg41894`, `OAI.UniversalTensorSquare.sg41900`, `OAI.UniversalTensorSquare.sg41932`, `OAI.UniversalTensorSquare.sg41940`, `OAI.UniversalTensorSquare.sg41956`, `OAI.UniversalTensorSquare.sg41958`, `OAI.UniversalTensorSquare.sg41962`, `OAI.UniversalTensorSquare.sg41968`, `OAI.UniversalTensorSquare.sg41983`, `OAI.UniversalTensorSquare.sg41991`, `OAI.UniversalTensorSquare.sg42004`, `OAI.UniversalTensorSquare.sg42015`, `OAI.UniversalTensorSquare.sg42019`, `OAI.UniversalTensorSquare.sg42022`, `OAI.UniversalTensorSquare.sg42026`, `OAI.UniversalTensorSquare.sg42027`, `OAI.UniversalTensorSquare.sg42056`, `OAI.UniversalTensorSquare.sg42059`, `OAI.UniversalTensorSquare.sg42066`, `OAI.UniversalTensorSquare.sg42068`, `OAI.UniversalTensorSquare.sg42076`, `OAI.UniversalTensorSquare.sg42079`, `OAI.UniversalTensorSquare.sg42084`, `OAI.UniversalTensorSquare.sg42085`, `OAI.UniversalTensorSquare.sg42088`, `OAI.UniversalTensorSquare.sg42091`, `OAI.UniversalTensorSquare.sg42106`, `OAI.UniversalTensorSquare.sg42127`, `OAI.UniversalTensorSquare.sg42132`, `OAI.UniversalTensorSquare.sg42167`, `OAI.UniversalTensorSquare.sg42172`, `OAI.UniversalTensorSquare.sg42173`, `OAI.UniversalTensorSquare.sg42174`, `OAI.UniversalTensorSquare.sg42197`, `OAI.UniversalTensorSquare.sg42216`, `OAI.UniversalTensorSquare.sg42239`, `OAI.UniversalTensorSquare.sg42243`, `OAI.UniversalTensorSquare.sg42267`, `OAI.UniversalTensorSquare.sg42272`, `OAI.UniversalTensorSquare.sg42281`, `OAI.UniversalTensorSquare.sg42282`, `OAI.UniversalTensorSquare.sg42287`, `OAI.UniversalTensorSquare.sg42296`, `OAI.UniversalTensorSquare.sg42326`, `OAI.UniversalTensorSquare.sg42336`, `OAI.UniversalTensorSquare.sg42337`, `OAI.UniversalTensorSquare.sg42339`, `OAI.UniversalTensorSquare.sg42347`, `OAI.UniversalTensorSquare.sg42349`, `OAI.UniversalTensorSquare.sg42360`, `OAI.UniversalTensorSquare.sg42371`, `OAI.UniversalTensorSquare.sg42375`, `OAI.UniversalTensorSquare.sg42459`, `OAI.UniversalTensorSquare.sg42484`, `OAI.UniversalTensorSquare.sg42490`, `OAI.UniversalTensorSquare.sg42513`, `OAI.UniversalTensorSquare.sg42522`, `OAI.UniversalTensorSquare.sg42524`, `OAI.UniversalTensorSquare.sg42528`, `OAI.UniversalTensorSquare.sg42529`, `OAI.UniversalTensorSquare.sg42535`, `OAI.UniversalTensorSquare.sg42536`, `OAI.UniversalTensorSquare.sg42562`, `OAI.UniversalTensorSquare.sg42563`, `OAI.UniversalTensorSquare.sg42567`, `OAI.UniversalTensorSquare.sg42581`, `OAI.UniversalTensorSquare.sg42589`, `OAI.UniversalTensorSquare.sg42593`, `OAI.UniversalTensorSquare.sg42604`, `OAI.UniversalTensorSquare.sg42608`, `OAI.UniversalTensorSquare.sg42612`, `OAI.UniversalTensorSquare.sg42621`, `OAI.UniversalTensorSquare.sg42625`, `OAI.UniversalTensorSquare.sg42627`, `OAI.UniversalTensorSquare.sg42628`, `OAI.UniversalTensorSquare.sg42630`, `OAI.UniversalTensorSquare.sg42637`, `OAI.UniversalTensorSquare.sg42640`, `OAI.UniversalTensorSquare.sg42651`, `OAI.UniversalTensorSquare.sg42661`, `OAI.UniversalTensorSquare.sg42662`, `OAI.UniversalTensorSquare.sg42663`, `OAI.UniversalTensorSquare.sg42667`, `OAI.UniversalTensorSquare.sg42670`, `OAI.UniversalTensorSquare.sg42671`, `OAI.UniversalTensorSquare.sg42675`, `OAI.UniversalTensorSquare.sg42678`, `OAI.UniversalTensorSquare.sg42681`, `OAI.UniversalTensorSquare.sg42683`, `OAI.UniversalTensorSquare.sg42685`, `OAI.UniversalTensorSquare.sg42687`, `OAI.UniversalTensorSquare.sg42689`, `OAI.UniversalTensorSquare.sg42691`, `OAI.UniversalTensorSquare.sg42704`, `OAI.UniversalTensorSquare.sg42706`, `OAI.UniversalTensorSquare.sg42720`, `OAI.UniversalTensorSquare.sg42729`, `OAI.UniversalTensorSquare.sg42732`, `OAI.UniversalTensorSquare.sg42736`, `OAI.UniversalTensorSquare.sg42740`, `OAI.UniversalTensorSquare.sg42747`, `OAI.UniversalTensorSquare.sg42750`, `OAI.UniversalTensorSquare.sg42751`, `OAI.UniversalTensorSquare.sg42754`, `OAI.UniversalTensorSquare.sg42755`, `OAI.UniversalTensorSquare.sg42758`, `OAI.UniversalTensorSquare.sg42763`, `OAI.UniversalTensorSquare.sg42765`, `OAI.UniversalTensorSquare.sg42766`, `OAI.UniversalTensorSquare.sg42768`, `OAI.UniversalTensorSquare.sg42772`, `OAI.UniversalTensorSquare.sg42775`, `OAI.UniversalTensorSquare.sg42792`, `OAI.UniversalTensorSquare.sg42809`, `OAI.UniversalTensorSquare.sg42810`, `OAI.UniversalTensorSquare.sg42824`, `OAI.UniversalTensorSquare.sg42825`, `OAI.UniversalTensorSquare.sg42829`, `OAI.UniversalTensorSquare.sg42833`, `OAI.UniversalTensorSquare.sg42834`, `OAI.UniversalTensorSquare.sg42838`, `OAI.UniversalTensorSquare.sg42839`, `OAI.UniversalTensorSquare.sg42842`, `OAI.UniversalTensorSquare.sg42861`, `OAI.UniversalTensorSquare.sg42863`, `OAI.UniversalTensorSquare.sg42875`, `OAI.UniversalTensorSquare.sg42880`, `OAI.UniversalTensorSquare.sg42881`, `OAI.UniversalTensorSquare.sg42889`, `OAI.UniversalTensorSquare.sg42895`, `OAI.UniversalTensorSquare.sg42900`, `OAI.UniversalTensorSquare.sg42901`, `OAI.UniversalTensorSquare.sg42911`, `OAI.UniversalTensorSquare.sg42912`, `OAI.UniversalTensorSquare.sg42915`, `OAI.UniversalTensorSquare.sg42917`, `OAI.UniversalTensorSquare.sg42921`, `OAI.UniversalTensorSquare.sg42938`, `OAI.UniversalTensorSquare.sg42939`, `OAI.UniversalTensorSquare.sg42953`, `OAI.UniversalTensorSquare.sg42954`, `OAI.UniversalTensorSquare.sg42961`, `OAI.UniversalTensorSquare.sg42962`, `OAI.UniversalTensorSquare.sg42970`, `OAI.UniversalTensorSquare.sg42973`, `OAI.UniversalTensorSquare.sg42974`, `OAI.UniversalTensorSquare.sg42983`, `OAI.UniversalTensorSquare.sg42986`, `OAI.UniversalTensorSquare.sg42989`, `OAI.UniversalTensorSquare.sg42990`, `OAI.UniversalTensorSquare.sg42995`, `OAI.UniversalTensorSquare.sg42996`, `OAI.UniversalTensorSquare.sg43003`, `OAI.UniversalTensorSquare.sg43013`, `OAI.UniversalTensorSquare.sg43016`, `OAI.UniversalTensorSquare.sg43020`, `OAI.UniversalTensorSquare.sg43022`, `OAI.UniversalTensorSquare.sg43024`, `OAI.UniversalTensorSquare.sg43025`, `OAI.UniversalTensorSquare.sg43027`, `OAI.UniversalTensorSquare.sg43030`, `OAI.UniversalTensorSquare.sg43033`, `OAI.UniversalTensorSquare.sg43034`, `OAI.UniversalTensorSquare.sg43035`, `OAI.UniversalTensorSquare.sg43041`, `OAI.UniversalTensorSquare.sg43044`, `OAI.UniversalTensorSquare.sg43048`, `OAI.UniversalTensorSquare.sg43049`, `OAI.UniversalTensorSquare.sg43050`, `OAI.UniversalTensorSquare.sg43053`, `OAI.UniversalTensorSquare.sg43054`, `OAI.UniversalTensorSquare.sg43060`, `OAI.UniversalTensorSquare.sg43061`, `OAI.UniversalTensorSquare.sg43068`, `OAI.UniversalTensorSquare.sg43072`, `OAI.UniversalTensorSquare.sg43073`, `OAI.UniversalTensorSquare.sg43076`, `OAI.UniversalTensorSquare.sg43077`, `OAI.UniversalTensorSquare.sg43080`, `OAI.UniversalTensorSquare.sg43081`, `OAI.UniversalTensorSquare.sg43087`, `OAI.UniversalTensorSquare.sg43093`, `OAI.UniversalTensorSquare.sg43094`, `OAI.UniversalTensorSquare.sg43097`, `OAI.UniversalTensorSquare.sg43100`, `OAI.UniversalTensorSquare.sg43101`, `OAI.UniversalTensorSquare.sg43103`, `OAI.UniversalTensorSquare.sg43108`, `OAI.UniversalTensorSquare.sg43111`, `OAI.UniversalTensorSquare.sg43117`, `OAI.UniversalTensorSquare.sg43121`, `OAI.UniversalTensorSquare.sg43123`, `OAI.UniversalTensorSquare.sg43127`, `OAI.UniversalTensorSquare.sg43129`, `OAI.UniversalTensorSquare.sg43130`, `OAI.UniversalTensorSquare.sg43132`, `OAI.UniversalTensorSquare.sg43137`, `OAI.UniversalTensorSquare.sg43143`, `OAI.UniversalTensorSquare.sg43149`, `OAI.UniversalTensorSquare.sg43157`, `OAI.UniversalTensorSquare.sg43159`, `OAI.UniversalTensorSquare.sg43164`, `OAI.UniversalTensorSquare.sg43170`, `OAI.UniversalTensorSquare.sg43174`, `OAI.UniversalTensorSquare.sg43177`, `OAI.UniversalTensorSquare.sg43181`, `OAI.UniversalTensorSquare.sg43185`, `OAI.UniversalTensorSquare.sg43193`, `OAI.UniversalTensorSquare.sg43196`, `OAI.UniversalTensorSquare.sg43205`, `OAI.UniversalTensorSquare.sg43208`, `OAI.UniversalTensorSquare.sg43211`, `OAI.UniversalTensorSquare.sg43213`, `OAI.UniversalTensorSquare.sg43216`, `OAI.UniversalTensorSquare.sg43231`, `OAI.UniversalTensorSquare.sg43235`, `OAI.UniversalTensorSquare.sg43246`, `OAI.UniversalTensorSquare.sg435`, `OAI.UniversalTensorSquare.sg4719`, `OAI.UniversalTensorSquare.sg4734`, `OAI.UniversalTensorSquare.sg4736`, `OAI.UniversalTensorSquare.sg4797`, `OAI.UniversalTensorSquare.sg4857`, `OAI.UniversalTensorSquare.sg4860`, `OAI.UniversalTensorSquare.sg503`, `OAI.UniversalTensorSquare.sg5129`, `OAI.UniversalTensorSquare.sg52`, `OAI.UniversalTensorSquare.sg5298`, `OAI.UniversalTensorSquare.sg5515`, `OAI.UniversalTensorSquare.sg5629`, `OAI.UniversalTensorSquare.sg5630`, `OAI.UniversalTensorSquare.sg5631`, `OAI.UniversalTensorSquare.sg5632`, `OAI.UniversalTensorSquare.sg5633`, `OAI.UniversalTensorSquare.sg5715`, `OAI.UniversalTensorSquare.sg5718`, `OAI.UniversalTensorSquare.sg6147`, `OAI.UniversalTensorSquare.sg6405`, `OAI.UniversalTensorSquare.sg6522`, `OAI.UniversalTensorSquare.sg6640`, `OAI.UniversalTensorSquare.sg6641`, `OAI.UniversalTensorSquare.sg6642`, `OAI.UniversalTensorSquare.sg6670`, `OAI.UniversalTensorSquare.sg6676`, `OAI.UniversalTensorSquare.sg6677`, `OAI.UniversalTensorSquare.sg6681`, `OAI.UniversalTensorSquare.sg6682`, `OAI.UniversalTensorSquare.sg6683`, `OAI.UniversalTensorSquare.sg6684`, `OAI.UniversalTensorSquare.sg6688`, `OAI.UniversalTensorSquare.sg6689`, `OAI.UniversalTensorSquare.sg6771`, `OAI.UniversalTensorSquare.sg6772`, `OAI.UniversalTensorSquare.sg6773`, `OAI.UniversalTensorSquare.sg6775`, `OAI.UniversalTensorSquare.sg6777`, `OAI.UniversalTensorSquare.sg6778`, `OAI.UniversalTensorSquare.sg6779`, `OAI.UniversalTensorSquare.sg6787`, `OAI.UniversalTensorSquare.sg6788`, `OAI.UniversalTensorSquare.sg6821`, `OAI.UniversalTensorSquare.sg6824`, `OAI.UniversalTensorSquare.sg6868`, `OAI.UniversalTensorSquare.sg6872`, `OAI.UniversalTensorSquare.sg6874`, `OAI.UniversalTensorSquare.sg6915`, `OAI.UniversalTensorSquare.sg6918`, `OAI.UniversalTensorSquare.sg6947`, `OAI.UniversalTensorSquare.sg703`, `OAI.UniversalTensorSquare.sg7080`, `OAI.UniversalTensorSquare.sg7085`, `OAI.UniversalTensorSquare.sg7089`, `OAI.UniversalTensorSquare.sg7096`, `OAI.UniversalTensorSquare.sg7099`, `OAI.UniversalTensorSquare.sg7156`, `OAI.UniversalTensorSquare.sg7213`, `OAI.UniversalTensorSquare.sg7218`, `OAI.UniversalTensorSquare.sg7247`, `OAI.UniversalTensorSquare.sg7250`, `OAI.UniversalTensorSquare.sg7252`, `OAI.UniversalTensorSquare.sg7269`, `OAI.UniversalTensorSquare.sg7307`, `OAI.UniversalTensorSquare.sg7315`, `OAI.UniversalTensorSquare.sg7341`, `OAI.UniversalTensorSquare.sg7347`, `OAI.UniversalTensorSquare.sg7349`, `OAI.UniversalTensorSquare.sg7350`, `OAI.UniversalTensorSquare.sg7356`, `OAI.UniversalTensorSquare.sg7357`, `OAI.UniversalTensorSquare.sg7358`, `OAI.UniversalTensorSquare.sg7359`, `OAI.UniversalTensorSquare.sg7365`, `OAI.UniversalTensorSquare.sg749`, `OAI.UniversalTensorSquare.sg7528`, `OAI.UniversalTensorSquare.sg7563`, `OAI.UniversalTensorSquare.sg7575`, `OAI.UniversalTensorSquare.sg7578`, `OAI.UniversalTensorSquare.sg7579`, `OAI.UniversalTensorSquare.sg7580`, `OAI.UniversalTensorSquare.sg7582`, `OAI.UniversalTensorSquare.sg7583`, `OAI.UniversalTensorSquare.sg7585`, `OAI.UniversalTensorSquare.sg7587`, `OAI.UniversalTensorSquare.sg7588`, `OAI.UniversalTensorSquare.sg7589`, `OAI.UniversalTensorSquare.sg7590`, `OAI.UniversalTensorSquare.sg7591`, `OAI.UniversalTensorSquare.sg7646`, `OAI.UniversalTensorSquare.sg7648`, `OAI.UniversalTensorSquare.sg7649`, `OAI.UniversalTensorSquare.sg7650`, `OAI.UniversalTensorSquare.sg7651`, `OAI.UniversalTensorSquare.sg7652`, `OAI.UniversalTensorSquare.sg7653`, `OAI.UniversalTensorSquare.sg7654`, `OAI.UniversalTensorSquare.sg7655`, `OAI.UniversalTensorSquare.sg7656`, `OAI.UniversalTensorSquare.sg7657`, `OAI.UniversalTensorSquare.sg7658`, `OAI.UniversalTensorSquare.sg771`, `OAI.UniversalTensorSquare.sg7711`, `OAI.UniversalTensorSquare.sg7712`, `OAI.UniversalTensorSquare.sg7713`, `OAI.UniversalTensorSquare.sg7714`, `OAI.UniversalTensorSquare.sg7715`, `OAI.UniversalTensorSquare.sg7716`, `OAI.UniversalTensorSquare.sg7717`, `OAI.UniversalTensorSquare.sg7718`, `OAI.UniversalTensorSquare.sg7719`, `OAI.UniversalTensorSquare.sg778`, `OAI.UniversalTensorSquare.sg779`, `OAI.UniversalTensorSquare.sg7847`, `OAI.UniversalTensorSquare.sg7853`, `OAI.UniversalTensorSquare.sg7868`, `OAI.UniversalTensorSquare.sg7899`, `OAI.UniversalTensorSquare.sg7901`, `OAI.UniversalTensorSquare.sg7907`, `OAI.UniversalTensorSquare.sg7909`, `OAI.UniversalTensorSquare.sg7913`, `OAI.UniversalTensorSquare.sg7917`, `OAI.UniversalTensorSquare.sg7926`, `OAI.UniversalTensorSquare.sg7929`, `OAI.UniversalTensorSquare.sg7930`, `OAI.UniversalTensorSquare.sg7931`, `OAI.UniversalTensorSquare.sg7963`, `OAI.UniversalTensorSquare.sg7967`, `OAI.UniversalTensorSquare.sg7968`, `OAI.UniversalTensorSquare.sg7973`, `OAI.UniversalTensorSquare.sg7978`, `OAI.UniversalTensorSquare.sg798`, `OAI.UniversalTensorSquare.sg7991`, `OAI.UniversalTensorSquare.sg8011`, `OAI.UniversalTensorSquare.sg8012`, `OAI.UniversalTensorSquare.sg8013`, `OAI.UniversalTensorSquare.sg8018`, `OAI.UniversalTensorSquare.sg8430`, `OAI.UniversalTensorSquare.sg8465`, `OAI.UniversalTensorSquare.sg8467`, `OAI.UniversalTensorSquare.sg8559`, `OAI.UniversalTensorSquare.sg8626`, `OAI.UniversalTensorSquare.sg8665`, `OAI.UniversalTensorSquare.sg8682`, `OAI.UniversalTensorSquare.sg8783`, `OAI.UniversalTensorSquare.sg9031`, `OAI.UniversalTensorSquare.sg9035`, `OAI.UniversalTensorSquare.sg9093`, `OAI.UniversalTensorSquare.sg9095`, `OAI.UniversalTensorSquare.sg9108`, `OAI.UniversalTensorSquare.sg9140`, `OAI.UniversalTensorSquare.sg9240`, `OAI.UniversalTensorSquare.sg9245`, `OAI.UniversalTensorSquare.sg9247`, `OAI.UniversalTensorSquare.sg9259`, `OAI.UniversalTensorSquare.sg9349`, `OAI.UniversalTensorSquare.sg9350`, `OAI.UniversalTensorSquare.sg9358`, `OAI.UniversalTensorSquare.sg9359`, `OAI.UniversalTensorSquare.sg9457`, `OAI.UniversalTensorSquare.sg9461`, `OAI.UniversalTensorSquare.sg9493`, `OAI.UniversalTensorSquare.sg9510`, `OAI.UniversalTensorSquare.sg9520`, `OAI.UniversalTensorSquare.sg9528`, `OAI.UniversalTensorSquare.sg9529`, `OAI.UniversalTensorSquare.sg9530`, `OAI.UniversalTensorSquare.sg9554`, `OAI.UniversalTensorSquare.sg9590`, `OAI.UniversalTensorSquare.sg9618`, `OAI.UniversalTensorSquare.sg9619`, `OAI.UniversalTensorSquare.sg9688`, `OAI.UniversalTensorSquare.sg9706`, `OAI.UniversalTensorSquare.sg9727`, `OAI.UniversalTensorSquare.sg9732`, `OAI.UniversalTensorSquare.sg9734`, `OAI.UniversalTensorSquare.sg9742`, `OAI.UniversalTensorSquare.sg9745`, `OAI.UniversalTensorSquare.sg9746`, `OAI.UniversalTensorSquare.sg9748`, `OAI.UniversalTensorSquare.sg9753`, `OAI.UniversalTensorSquare.sg9755`, `OAI.UniversalTensorSquare.sg9756`, `OAI.UniversalTensorSquare.sg9759`, `OAI.UniversalTensorSquare.sg9761`, `OAI.UniversalTensorSquare.sg9766`, `OAI.UniversalTensorSquare.sg9818`, `OAI.UniversalTensorSquare.sg9833`, `OAI.UniversalTensorSquare.sg9835` and `OAI.UniversalTensorSquare.sg9857`.
-- source:
--   OpenAI, Universal Tensor Squares for Symmetric Groups (result family 205), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 205; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ259US001
import Definitions.Def_OAIQ259US002
import Definitions.Def_OAIQ259US003

section
-- module Solutions.OAIQ259_US.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
end OAIVecTail
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_Intermediate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intermediate. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

def prefixBounds (M r d e : ℕ) : List (ℕ × ℕ) :=
  (if 1 < d then [(d-1,2*M-2)] else []) ++
    ((List.range 4).filterMap fun k =>
      let f := k+1
      let q := testWidth M f
      if e ≤ f ∧ 0 < q then some (q,2*r-2+q*(f+1)) else none)

instance instDecidableExceptionalPair (M r : ℕ) : Decidable (exceptionalPair M r) := inferInstanceAs
  (Decidable ((M = 10 ∧ 8 ≤ r ∧ r ≤ 17) ∨ (M = 12 ∧ 14 ≤ r ∧ r ≤ 20) ∨
    (M = 14 ∧ 22 ≤ r ∧ r ≤ 23)))

instance instDecidableAdmissibleR (M r : ℕ) : Decidable (admissibleR M r) := inferInstanceAs
  (Decidable (0 < r ∧ (if M % 2 = 1 then 2*r ≤ M-1 else 2*r ≤ 3*M+4) ∧
    ¬exceptionalPair M r))

def intermediateCheck (M r d e : ℕ) : Prop :=
  ∃ p ∈ prefixBounds M r d e, ∃ q ∈ prefixBounds M r e d,
    max (p.2+q.2-1) (p.2*q.2/(p.1*q.1)) < M*(M+1)/2+2*r

instance instDecidableIntermediateCheck (M r d e : ℕ) : Decidable (intermediateCheck M r d e) :=
  inferInstanceAs (Decidable (∃ p ∈ prefixBounds M r d e,
    ∃ q ∈ prefixBounds M r e d,
    max (p.2+q.2-1) (p.2*q.2/(p.1*q.1)) < M*(M+1)/2+2*r))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RefinedExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refined Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

instance instDecidableCoreImpossible (K d : ℕ) (A : List (ℕ × ℕ)) : Decidable (coreImpossible K d A) :=
  inferInstanceAs (Decidable (∃ p ∈ A, d ≤ p.1 ∧ p.2 < K))

def refinedCheck (n M r d e a b : ℕ) (q : List ℕ) : Prop :=
  let A := prefixBounds M r d e ++ [(a,(q.take a).sum-1)]
  let B := prefixBounds M r e d ++ [(b,(q.take b).sum-1)]
  coreImpossible (2*M-1) d A ∨ coreImpossible (2*M-1) e B ∨ impossibleBounds n A B

instance instDecidableRefinedCheck (n M r d e a b : ℕ) (q : List ℕ) : Decidable (refinedCheck n M r d e a b q) := by
  unfold refinedCheck; infer_instance

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_RowCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Certificates. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

instance instDecidableChainValid (rs : List ℕ) (cs : List (List ℕ)) (ss : List ℕ) : Decidable (ChainValid rs cs ss) := by
  induction cs generalizing rs with
  | nil => unfold ChainValid; infer_instance
  | cons us cs ih =>
    letI := ih us
    unfold ChainValid
    infer_instance

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_FiniteDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Diagrams. -/

section

namespace UniversalTensorSquare

lemma diagramOfCols_card (rs : List ℕ) (hs : rs.SortedGE)
    (hp : ∀ a ∈ rs, 0 < a) : (diagramOfCols rs hs).card = rs.sum := by
  rw [diagramOfCols, Saxl.transpose_card, Saxl.card_eq_sum_rowLens,
    YoungDiagram.rowLens_ofRowLens_eq_self hp]

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ConstrainedDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constrained Diagrams. -/

section

namespace UniversalTensorSquare
open Saxl

def rowsWithin (n : ℕ) (A B : List (ℕ × ℕ)) : List (List ℕ) :=
  (List.range' (minHeight n B) (firstBound n A + 1 - minHeight n B)).flatMap fun h =>
    constrainedRows h n (firstBound n B) A B

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_SentinelExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sentinel Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def residualCheck (n M r d e a b : ℕ) (q : List ℕ) (P : List ℕ → Prop) : Prop :=
  let A := prefixBounds M r d e ++ [(a,(q.take a).sum-1)]
  let B := prefixBounds M r e d ++ [(b,(q.take b).sum-1)]
  (d ≤ 4 ∧ coreImpossible (2*M-1) d A) ∨
    (e ≤ 4 ∧ coreImpossible (2*M-1) e B) ∨ impossibleBounds n A B ∨
    ∀ rs ∈ rowsWithin n A B, P rs

instance instDecidableResidualCheckOfDecidablePredListNat (n M r d e a b : ℕ) (q : List ℕ) (P : List ℕ → Prop) [DecidablePred P] :
    Decidable (residualCheck n M r d e a b q P) := by
  unfold residualCheck; infer_instance

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_NumericalSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Support. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

instance instDecidableRowsBand (M r : ℕ) (rs : List ℕ) : Decidable (RowsBand M r rs) := by
  unfold RowsBand; infer_instance

instance instDecidablePredListNatResidualProperty (M r : ℕ) (qs ls : List (List ℕ)) : DecidablePred (ResidualProperty M r qs ls) := by
  intro rs; unfold ResidualProperty; infer_instance

end UniversalTensorSquare

end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_RowSquareTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Square Tools. -/

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

instance instDecidableRowJoin (p q x y a b : List ℕ) : Decidable (RowJoin p q x y a b) := by
  unfold RowJoin; infer_instance

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RegionExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Region Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def semanticResidualCheck (n M r d e a b : ℕ) (q : List ℕ) (P : List ℕ → Prop) : Prop :=
  let A := prefixBounds M r d e ++ [(a,(q.take a).sum-1)]
  let B := prefixBounds M r e d ++ [(b,(q.take b).sum-1)]
  (d ≤ 4 ∧ coreImpossible (2*M-1) d A) ∨
    (e ≤ 4 ∧ coreImpossible (2*M-1) e B) ∨ impossibleBounds n A B ∨
    ∀ μ : YoungDiagram, μ.card = n → RowBounds μ.transpose A → RowBounds μ B → P μ.rowLens

instance instDecidableBoundsEntail (A B : List (ℕ × ℕ)) : Decidable (boundsEntail A B) := by
  unfold boundsEntail; infer_instance

def regionCheck (n M r d e a b : ℕ) (q : List ℕ) (regions : List PrefixRegion) : Prop :=
  let A := prefixBounds M r d e ++ [(a,(q.take a).sum-1)]
  let B := prefixBounds M r e d ++ [(b,(q.take b).sum-1)]
  (d ≤ 4 ∧ coreImpossible (2*M-1) d A) ∨
    (e ≤ 4 ∧ coreImpossible (2*M-1) e B) ∨ impossibleBounds n A B ∨
    ∃ R ∈ regions, boundsEntail A R.1 ∧ boundsEntail B R.2

instance instDecidableRegionCheck (n M r d e a b : ℕ) (q : List ℕ) (regions : List PrefixRegion) :
    Decidable (regionCheck n M r d e a b q regions) := by
  unfold regionCheck; infer_instance

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeEight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Eight. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

lemma eightWitness_card : eightWitness.card = 8 :=
  diagramOfCols_card _ _ (by simp)

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeFive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Five. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

lemma fiveWitness_card : fiveWitness.card = 5 :=
  diagramOfCols_card _ _ (by simp)

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ResidualTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Residual Trees. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

instance instDecidablePredListNatTreeResidual (M r : ℕ) (qs : List (List ℕ)) (t : RowTree) :
    DecidablePred (TreeResidual M r qs t) := by
  intro rs; unfold TreeResidual; infer_instance

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 116. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan116_0 : PackingPlan := (.join (.twoPaths 20 [11,11,11,11]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 10 3 [12,11]))))))

def degreePlan116_1 : PackingPlan := (.join (.twoPaths 20 [11,11,11,11]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 10 2))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 118. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan118_0 : PackingPlan := (.join (.neighbor 21 [11,11,11,10]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 11 1 [12,11]))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan16_0 : PackingPlan := (.join (.twoPaths 4 [3,3,3,3]) (.repeated 2 2))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan18_0 : PackingPlan := (.join (.neighbor 5 [3,3,3,2]) (.twosOdd 3 1 [4,3]))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan19_0 : PackingPlan := (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 3) (.twosOdd 2 1 [3,2])))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan20_0 : PackingPlan := (.join (.twoPaths 5 [4,4,3,3]) (.repeated 3 2))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan22_0 : PackingPlan := (.join (.neighbor 6 [4,3,3,3]) (.twosOdd 4 1 [5,4]))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan24_0 : PackingPlan := (.join (.twoPaths 6 [4,4,4,4]) (.repeated 4 2))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan26_0 : PackingPlan := (.join (.neighbor 7 [4,4,4,3]) (.twosOdd 5 1 [6,5]))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan31_0 : PackingPlan := (.join (.twoPaths 7 [5,5,4,4]) (.join (.repeated 1 4) (.twosOdd 3 3 [5,4])))

def degreePlan31_1 : PackingPlan := (.join (.twoPaths 7 [5,5,4,4]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 3 2)))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan35_0 : PackingPlan := (.join (.twoPaths 8 [5,5,5,5]) (.join (.repeated 1 4) (.twosOdd 4 3 [6,5])))

def degreePlan35_1 : PackingPlan := (.join (.twoPaths 8 [5,5,5,5]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 4 2)))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan37_0 : PackingPlan := (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 5 1 [6,5])))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan39_0 : PackingPlan := (.join (.twoPaths 9 [6,6,5,5]) (.join (.repeated 1 4) (.twosOdd 5 3 [7,6])))

def degreePlan39_1 : PackingPlan := (.join (.twoPaths 9 [6,6,5,5]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 5 2)))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan41_0 : PackingPlan := (.join (.neighbor 10 [6,5,5,5]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 6 1 [7,6])))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan43_0 : PackingPlan := (.join (.twoPaths 10 [6,6,6,6]) (.join (.repeated 1 4) (.twosOdd 6 3 [8,7])))

def degreePlan43_1 : PackingPlan := (.join (.twoPaths 10 [6,6,6,6]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 6 2)))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan58_0 : PackingPlan := (.join (.twoPaths 12 [7,7,7,7]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 6 3 [8,7]))))

def degreePlan58_1 : PackingPlan := (.join (.twoPaths 12 [7,7,7,7]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 6 2))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree62_190 : RowTree := (.node [11,11,10,8,5,4,4,3,1,1,1,1,1,1] (.node [11,11,10,8,5,4,3,3,3,1,1,1,1] (.node [11,11,10,8,5,4,3,3,2,1,1,1,1,1] (.node [11,11,10,8,5,4,3,2,2,2,2,2] (.node [11,11,10,8,5,4,3,2,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,10,8,5,4,3,3,2,2,2,1] (.node [11,11,10,8,5,4,3,3,2,2,1,1,1] .empty .empty) .empty)) (.node [11,11,10,8,5,4,4,2,2,2,1,1,1] (.node [11,11,10,8,5,4,4,2,2,1,1,1,1,1] (.node [11,11,10,8,5,4,3,3,3,2,1,1] .empty .empty) .empty) (.node [11,11,10,8,5,4,4,2,2,2,2,1] .empty .empty))) (.node [11,11,10,8,5,5,2,2,2,2,1,1,1,1] (.node [11,11,10,8,5,4,4,3,3,1,1,1] (.node [11,11,10,8,5,4,4,3,2,2,1,1] (.node [11,11,10,8,5,4,4,3,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,5,4,4,4,2,1,1,1] (.node [11,11,10,8,5,4,4,4,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,8,5,5,3,2,2,1,1,1,1,1] (.node [11,11,10,8,5,5,2,2,2,2,2,2] (.node [11,11,10,8,5,5,2,2,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,10,8,5,5,3,2,2,2,1,1,1] .empty .empty))))

def degreeTree62_191 : RowTree := (.node [11,11,10,8,5,5,5,1,1,1,1,1,1,1] (.node [11,11,10,8,5,5,4,2,2,1,1,1,1] (.node [11,11,10,8,5,5,3,3,2,2,1,1] (.node [11,11,10,8,5,5,3,3,2,1,1,1,1] (.node [11,11,10,8,5,5,3,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,5,5,4,2,1,1,1,1,1,1] (.node [11,11,10,8,5,5,3,3,3,1,1,1] .empty .empty) .empty)) (.node [11,11,10,8,5,5,4,3,2,1,1,1] (.node [11,11,10,8,5,5,4,3,1,1,1,1,1] (.node [11,11,10,8,5,5,4,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,10,8,5,5,4,4,1,1,1,1] .empty .empty))) (.node [11,11,10,8,6,3,2,2,2,2,2,1,1,1] (.node [11,11,10,8,5,5,5,3,1,1,1,1] (.node [11,11,10,8,5,5,5,2,2,1,1,1] (.node [11,11,10,8,5,5,5,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,6,2,2,2,2,2,2,2,2] (.node [11,11,10,8,6,2,2,2,2,2,2,2,1,1] .empty .empty) .empty)) (.node [11,11,10,8,6,3,3,2,2,2,2,1,1] (.node [11,11,10,8,6,3,3,2,2,2,1,1,1,1] (.node [11,11,10,8,6,3,2,2,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,10,8,6,3,3,2,2,2,2,2] .empty .empty))))

def degreeTree62_192 : RowTree := (.node [11,11,10,8,5,5,3,2,2,2,2,1] degreeTree62_190 degreeTree62_191)

def degreeTree62_193 : RowTree := (.node [11,11,10,8,6,4,3,3,1,1,1,1,1,1] (.node [11,11,10,8,6,4,2,2,2,2,2,1,1] (.node [11,11,10,8,6,3,3,3,3,1,1,1,1] (.node [11,11,10,8,6,3,3,3,2,2,2,1] (.node [11,11,10,8,6,3,3,3,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,6,4,2,2,2,2,1,1,1,1] (.node [11,11,10,8,6,3,3,3,3,2,1,1] .empty .empty) .empty)) (.node [11,11,10,8,6,4,3,2,2,2,1,1,1] (.node [11,11,10,8,6,4,3,2,2,1,1,1,1,1] (.node [11,11,10,8,6,4,2,2,2,2,2,2] .empty .empty) .empty) (.node [11,11,10,8,6,4,3,2,2,2,2,1] .empty .empty))) (.node [11,11,10,8,6,4,4,2,2,2,1,1] (.node [11,11,10,8,6,4,3,3,3,1,1,1] (.node [11,11,10,8,6,4,3,3,2,2,1,1] (.node [11,11,10,8,6,4,3,3,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,6,4,4,2,2,1,1,1,1] (.node [11,11,10,8,6,4,4,2,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,8,6,4,4,4,1,1,1,1] (.node [11,11,10,8,6,4,4,3,2,1,1,1] (.node [11,11,10,8,6,4,4,3,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,6,5,2,2,2,1,1,1,1,1] .empty .empty))))

def degreeTree62_194 : RowTree := (.node [11,11,10,8,6,5,5,1,1,1,1,1,1] (.node [11,11,10,8,6,5,3,3,2,1,1,1] (.node [11,11,10,8,6,5,3,2,2,1,1,1,1] (.node [11,11,10,8,6,5,3,2,1,1,1,1,1,1] (.node [11,11,10,8,6,5,2,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,10,8,6,5,3,3,1,1,1,1,1] (.node [11,11,10,8,6,5,3,2,2,2,1,1] .empty .empty) .empty)) (.node [11,11,10,8,6,5,4,2,2,1,1,1] (.node [11,11,10,8,6,5,4,2,1,1,1,1,1] (.node [11,11,10,8,6,5,4,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,6,5,4,3,1,1,1,1] .empty .empty))) (.node [11,11,10,8,6,6,3,2,1,1,1,1,1] (.node [11,11,10,8,6,6,2,2,2,1,1,1,1] (.node [11,11,10,8,6,6,2,2,1,1,1,1,1,1] (.node [11,11,10,8,6,5,5,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,6,6,3,1,1,1,1,1,1,1] (.node [11,11,10,8,6,6,2,2,2,2,1,1] .empty .empty) .empty)) (.node [11,11,10,8,6,6,4,1,1,1,1,1,1] (.node [11,11,10,8,6,6,3,3,1,1,1,1] (.node [11,11,10,8,6,6,3,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,6,6,4,2,1,1,1,1] .empty .empty))))

def degreeTree62_195 : RowTree := (.node [11,11,10,8,6,5,2,2,2,2,1,1,1] degreeTree62_193 degreeTree62_194)

def degreeTree62_196 : RowTree := (.node [11,11,10,8,6,3,3,3,2,1,1,1,1,1] degreeTree62_192 degreeTree62_195)

def degreeTree62_197 : RowTree := (.node [11,11,10,8,7,3,3,3,2,2,1,1] (.node [11,11,10,8,7,3,3,2,2,1,1,1,1,1] (.node [11,11,10,8,7,3,2,2,2,2,1,1,1,1] (.node [11,11,10,8,7,2,2,2,2,2,2,2,1] (.node [11,11,10,8,7,2,2,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,7,3,2,2,2,2,2,2] (.node [11,11,10,8,7,3,2,2,2,2,2,1,1] .empty .empty) .empty)) (.node [11,11,10,8,7,3,3,3,1,1,1,1,1,1] (.node [11,11,10,8,7,3,3,2,2,2,2,1] (.node [11,11,10,8,7,3,3,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,7,3,3,3,2,1,1,1,1] .empty .empty))) (.node [11,11,10,8,7,4,3,2,2,1,1,1,1] (.node [11,11,10,8,7,4,2,2,2,2,1,1,1] (.node [11,11,10,8,7,4,2,2,2,1,1,1,1,1] (.node [11,11,10,8,7,3,3,3,3,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,7,4,3,2,1,1,1,1,1,1] (.node [11,11,10,8,7,4,2,2,2,2,2,1] .empty .empty) .empty)) (.node [11,11,10,8,7,4,3,3,2,1,1,1] (.node [11,11,10,8,7,4,3,3,1,1,1,1,1] (.node [11,11,10,8,7,4,3,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,10,8,7,4,4,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_198 : RowTree := (.node [11,11,10,8,7,5,4,2,1,1,1,1] (.node [11,11,10,8,7,5,3,1,1,1,1,1,1,1] (.node [11,11,10,8,7,5,2,2,1,1,1,1,1,1] (.node [11,11,10,8,7,4,4,3,1,1,1,1] (.node [11,11,10,8,7,4,4,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,7,5,2,2,2,2,1,1] (.node [11,11,10,8,7,5,2,2,2,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,8,7,5,3,3,1,1,1,1] (.node [11,11,10,8,7,5,3,2,2,1,1,1] (.node [11,11,10,8,7,5,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,7,5,4,1,1,1,1,1,1] .empty .empty))) (.node [11,11,10,8,7,6,3,2,1,1,1,1] (.node [11,11,10,8,7,6,2,2,1,1,1,1,1] (.node [11,11,10,8,7,6,2,1,1,1,1,1,1,1] (.node [11,11,10,8,7,5,5,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,7,6,3,1,1,1,1,1,1] (.node [11,11,10,8,7,6,2,2,2,1,1,1] .empty .empty) .empty)) (.node [11,11,10,8,7,7,2,1,1,1,1,1,1] (.node [11,11,10,8,7,7,1,1,1,1,1,1,1,1] (.node [11,11,10,8,7,6,4,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,7,7,2,2,1,1,1,1] .empty .empty))))

def degreeTree62_199 : RowTree := (.node [11,11,10,8,7,4,4,2,1,1,1,1,1] degreeTree62_197 degreeTree62_198)

def degreeTree62_200 : RowTree := (.node [11,11,10,8,8,3,3,3,2,1,1,1] (.node [11,11,10,8,8,3,2,2,2,2,2,1] (.node [11,11,10,8,8,2,2,2,2,2,2,2] (.node [11,11,10,8,8,2,2,2,2,2,2,1,1] (.node [11,11,10,8,8,2,2,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,8,3,2,2,2,2,1,1,1] (.node [11,11,10,8,8,3,2,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,8,8,3,3,2,2,2,1,1] (.node [11,11,10,8,8,3,3,2,2,1,1,1,1] (.node [11,11,10,8,8,3,3,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,8,3,3,3,1,1,1,1,1] .empty .empty))) (.node [11,11,10,8,8,4,3,2,2,1,1,1] (.node [11,11,10,8,8,4,2,2,2,2,1,1] (.node [11,11,10,8,8,4,2,2,2,1,1,1,1] (.node [11,11,10,8,8,4,2,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,8,4,3,2,1,1,1,1,1] (.node [11,11,10,8,8,4,3,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,8,8,4,4,2,1,1,1,1] (.node [11,11,10,8,8,4,4,1,1,1,1,1,1] (.node [11,11,10,8,8,4,3,3,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,8,5,2,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_201 : RowTree := (.node [11,11,10,8,8,8,1,1,1,1,1,1] (.node [11,11,10,8,8,6,2,1,1,1,1,1,1] (.node [11,11,10,8,8,5,3,2,1,1,1,1] (.node [11,11,10,8,8,5,3,1,1,1,1,1,1] (.node [11,11,10,8,8,5,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,8,6,1,1,1,1,1,1,1,1] (.node [11,11,10,8,8,5,4,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,8,8,7,1,1,1,1,1,1,1] (.node [11,11,10,8,8,6,3,1,1,1,1,1] (.node [11,11,10,8,8,6,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,8,8,7,2,1,1,1,1,1] .empty .empty))) (.node [11,11,10,9,4,3,3,2,2,2,2,1,1,1] (.node [11,11,10,9,3,3,3,3,3,3,3] (.node [11,11,10,9,3,3,3,3,3,2,2,1,1] (.node [11,11,10,9,3,3,3,2,2,2,2,2,2] .empty .empty) .empty) (.node [11,11,10,9,4,3,2,2,2,2,2,2,2] (.node [11,11,10,9,4,2,2,2,2,2,2,2,2,1] .empty .empty) .empty)) (.node [11,11,10,9,4,3,3,3,3,1,1,1,1,1] (.node [11,11,10,9,4,3,3,3,2,2,2,1,1] (.node [11,11,10,9,4,3,3,2,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,10,9,4,3,3,3,3,2,1,1,1] .empty .empty))))

def degreeTree62_202 : RowTree := (.node [11,11,10,8,8,5,2,2,1,1,1,1,1] degreeTree62_200 degreeTree62_201)

def degreeTree62_203 : RowTree := (.node [11,11,10,8,7,7,3,1,1,1,1,1] degreeTree62_199 degreeTree62_202)

def degreeTree62_204 : RowTree := (.node [11,11,10,8,6,6,5,1,1,1,1,1] degreeTree62_196 degreeTree62_203)

def degreeTree62_205 : RowTree := (.node [11,11,10,9,4,4,4,2,2,1,1,1,1,1] (.node [11,11,10,9,4,4,3,3,2,1,1,1,1,1] (.node [11,11,10,9,4,4,3,2,2,2,1,1,1,1] (.node [11,11,10,9,4,4,2,2,2,2,2,2,1] (.node [11,11,10,9,4,4,2,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,4,4,3,2,2,2,2,2] (.node [11,11,10,9,4,4,3,2,2,2,2,1,1] .empty .empty) .empty)) (.node [11,11,10,9,4,4,3,3,3,1,1,1,1] (.node [11,11,10,9,4,4,3,3,2,2,2,1] (.node [11,11,10,9,4,4,3,3,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,4,4,3,3,3,2,1,1] .empty .empty))) (.node [11,11,10,9,4,4,4,3,3,1,1,1] (.node [11,11,10,9,4,4,4,3,1,1,1,1,1,1] (.node [11,11,10,9,4,4,4,2,2,2,2,1] (.node [11,11,10,9,4,4,4,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,4,4,4,3,2,2,1,1] (.node [11,11,10,9,4,4,4,3,2,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,9,5,2,2,2,2,2,2,2,1,1] (.node [11,11,10,9,4,4,4,4,2,1,1,1] (.node [11,11,10,9,4,4,4,4,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,5,2,2,2,2,2,2,2,2] .empty .empty))))

def degreeTree62_206 : RowTree := (.node [11,11,10,9,5,4,2,2,2,2,2,1,1] (.node [11,11,10,9,5,3,3,3,2,2,1,1,1] (.node [11,11,10,9,5,3,3,2,2,2,2,1,1] (.node [11,11,10,9,5,3,3,2,2,2,1,1,1,1] (.node [11,11,10,9,5,3,2,2,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,10,9,5,3,3,3,2,1,1,1,1,1] (.node [11,11,10,9,5,3,3,2,2,2,2,2] .empty .empty) .empty)) (.node [11,11,10,9,5,3,3,3,3,2,1,1] (.node [11,11,10,9,5,3,3,3,3,1,1,1,1] (.node [11,11,10,9,5,3,3,3,2,2,2,1] .empty .empty) .empty) (.node [11,11,10,9,5,4,2,2,2,2,1,1,1,1] .empty .empty))) (.node [11,11,10,9,5,4,3,3,2,1,1,1,1] (.node [11,11,10,9,5,4,3,2,2,2,1,1,1] (.node [11,11,10,9,5,4,3,2,2,1,1,1,1,1] (.node [11,11,10,9,5,4,2,2,2,2,2,2] .empty .empty) .empty) (.node [11,11,10,9,5,4,3,3,1,1,1,1,1,1] (.node [11,11,10,9,5,4,3,2,2,2,2,1] .empty .empty) .empty)) (.node [11,11,10,9,5,4,4,2,1,1,1,1,1,1] (.node [11,11,10,9,5,4,3,3,3,1,1,1] (.node [11,11,10,9,5,4,3,3,2,2,1,1] .empty .empty) .empty) (.node [11,11,10,9,5,4,4,2,2,1,1,1,1] .empty .empty))))

def degreeTree62_207 : RowTree := (.node [11,11,10,9,5,3,2,2,2,2,2,1,1,1] degreeTree62_205 degreeTree62_206)

def degreeTree62_208 : RowTree := (.node [11,11,10,9,5,5,3,3,2,1,1,1] (.node [11,11,10,9,5,5,2,2,2,2,2,1] (.node [11,11,10,9,5,4,4,4,1,1,1,1] (.node [11,11,10,9,5,4,4,3,2,1,1,1] (.node [11,11,10,9,5,4,4,3,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,5,5,2,2,2,2,1,1,1] (.node [11,11,10,9,5,5,2,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,9,5,5,3,2,2,2,1,1] (.node [11,11,10,9,5,5,3,2,2,1,1,1,1] (.node [11,11,10,9,5,5,3,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,5,5,3,3,1,1,1,1,1] .empty .empty))) (.node [11,11,10,9,5,5,5,2,1,1,1,1] (.node [11,11,10,9,5,5,4,2,2,1,1,1] (.node [11,11,10,9,5,5,4,2,1,1,1,1,1] (.node [11,11,10,9,5,5,4,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,5,5,5,1,1,1,1,1,1] (.node [11,11,10,9,5,5,4,3,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,9,6,3,2,2,2,2,1,1,1,1] (.node [11,11,10,9,6,2,2,2,2,2,2,2,1] (.node [11,11,10,9,6,2,2,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,6,3,2,2,2,2,2,1,1] .empty .empty))))

def degreeTree62_209 : RowTree := (.node [11,11,10,9,6,4,3,2,1,1,1,1,1,1] (.node [11,11,10,9,6,3,3,3,2,2,1,1] (.node [11,11,10,9,6,3,3,2,2,2,2,1] (.node [11,11,10,9,6,3,3,2,2,2,1,1,1] (.node [11,11,10,9,6,3,3,2,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,6,3,3,3,2,1,1,1,1] (.node [11,11,10,9,6,3,3,3,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,9,6,4,2,2,2,2,1,1,1] (.node [11,11,10,9,6,4,2,2,2,1,1,1,1,1] (.node [11,11,10,9,6,3,3,3,3,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,6,4,2,2,2,2,2,1] .empty .empty))) (.node [11,11,10,9,6,4,4,2,1,1,1,1,1] (.node [11,11,10,9,6,4,3,3,1,1,1,1,1] (.node [11,11,10,9,6,4,3,2,2,2,1,1] (.node [11,11,10,9,6,4,3,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,6,4,4,1,1,1,1,1,1,1] (.node [11,11,10,9,6,4,3,3,2,1,1,1] .empty .empty) .empty)) (.node [11,11,10,9,6,5,2,2,1,1,1,1,1,1] (.node [11,11,10,9,6,4,4,3,1,1,1,1] (.node [11,11,10,9,6,4,4,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,6,5,2,2,2,1,1,1,1] .empty .empty))))

def degreeTree62_210 : RowTree := (.node [11,11,10,9,6,3,2,2,2,2,2,2] degreeTree62_208 degreeTree62_209)

def degreeTree62_211 : RowTree := (.node [11,11,10,9,5,4,4,2,2,2,1,1] degreeTree62_207 degreeTree62_210)

def degreeTree62_212 : RowTree := (.node [11,11,10,9,6,6,3,1,1,1,1,1,1] (.node [11,11,10,9,6,5,4,2,1,1,1,1] (.node [11,11,10,9,6,5,3,2,2,1,1,1] (.node [11,11,10,9,6,5,3,2,1,1,1,1,1] (.node [11,11,10,9,6,5,3,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,6,5,4,1,1,1,1,1,1] (.node [11,11,10,9,6,5,3,3,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,9,6,6,2,2,1,1,1,1,1] (.node [11,11,10,9,6,6,2,1,1,1,1,1,1,1] (.node [11,11,10,9,6,5,5,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,6,6,2,2,2,1,1,1] .empty .empty))) (.node [11,11,10,9,7,3,2,2,2,1,1,1,1,1] (.node [11,11,10,9,7,2,2,2,2,2,1,1,1,1] (.node [11,11,10,9,6,6,4,1,1,1,1,1] (.node [11,11,10,9,6,6,3,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,7,2,2,2,2,2,2,2] (.node [11,11,10,9,7,2,2,2,2,2,2,1,1] .empty .empty) .empty)) (.node [11,11,10,9,7,3,3,2,1,1,1,1,1,1] (.node [11,11,10,9,7,3,2,2,2,2,2,1] (.node [11,11,10,9,7,3,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,7,3,3,2,2,1,1,1,1] .empty .empty))))

def degreeTree62_213 : RowTree := (.node [11,11,10,9,7,4,4,2,1,1,1,1] (.node [11,11,10,9,7,4,3,1,1,1,1,1,1,1] (.node [11,11,10,9,7,4,2,2,1,1,1,1,1,1] (.node [11,11,10,9,7,3,3,3,2,1,1,1] (.node [11,11,10,9,7,3,3,3,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,7,4,2,2,2,2,1,1] (.node [11,11,10,9,7,4,2,2,2,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,9,7,4,3,3,1,1,1,1] (.node [11,11,10,9,7,4,3,2,2,1,1,1] (.node [11,11,10,9,7,4,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,7,4,4,1,1,1,1,1,1] .empty .empty))) (.node [11,11,10,9,7,5,4,1,1,1,1,1] (.node [11,11,10,9,7,5,2,2,2,1,1,1] (.node [11,11,10,9,7,5,2,2,1,1,1,1,1] (.node [11,11,10,9,7,5,2,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,7,5,3,2,1,1,1,1] (.node [11,11,10,9,7,5,3,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,9,7,6,2,2,1,1,1,1] (.node [11,11,10,9,7,6,2,1,1,1,1,1,1] (.node [11,11,10,9,7,6,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,7,6,3,1,1,1,1,1] .empty .empty))))

def degreeTree62_214 : RowTree := (.node [11,11,10,9,7,3,3,2,2,2,1,1] degreeTree62_212 degreeTree62_213)

def degreeTree62_215 : RowTree := (.node [11,11,10,9,8,3,3,3,1,1,1,1] (.node [11,11,10,9,8,3,2,2,2,1,1,1,1] (.node [11,11,10,9,8,2,2,2,2,2,1,1,1] (.node [11,11,10,9,8,2,2,2,2,1,1,1,1,1] (.node [11,11,10,9,7,7,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,8,3,2,2,1,1,1,1,1,1] (.node [11,11,10,9,8,2,2,2,2,2,2,1] .empty .empty) .empty)) (.node [11,11,10,9,8,3,3,2,1,1,1,1,1] (.node [11,11,10,9,8,3,3,1,1,1,1,1,1,1] (.node [11,11,10,9,8,3,2,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,10,9,8,3,3,2,2,1,1,1] .empty .empty))) (.node [11,11,10,9,8,4,4,1,1,1,1,1] (.node [11,11,10,9,8,4,2,2,2,1,1,1] (.node [11,11,10,9,8,4,2,2,1,1,1,1,1] (.node [11,11,10,9,8,4,2,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,8,4,3,2,1,1,1,1] (.node [11,11,10,9,8,4,3,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,9,8,5,2,2,1,1,1,1] (.node [11,11,10,9,8,5,2,1,1,1,1,1,1] (.node [11,11,10,9,8,5,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,8,5,3,1,1,1,1,1] .empty .empty))))

def degreeTree62_216 : RowTree := (.node [11,11,10,9,9,4,1,1,1,1,1,1,1,1] (.node [11,11,10,9,9,3,2,1,1,1,1,1,1,1] (.node [11,11,10,9,9,2,2,2,1,1,1,1,1,1] (.node [11,11,10,9,8,7,1,1,1,1,1,1] (.node [11,11,10,9,8,6,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,9,2,2,2,2,2,1,1] (.node [11,11,10,9,9,2,2,2,2,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,9,9,3,3,1,1,1,1,1,1] (.node [11,11,10,9,9,3,2,2,2,1,1,1] (.node [11,11,10,9,9,3,2,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,9,3,3,2,1,1,1,1] .empty .empty))) (.node [11,11,10,9,9,5,2,1,1,1,1,1] (.node [11,11,10,9,9,4,3,1,1,1,1,1] (.node [11,11,10,9,9,4,2,2,1,1,1,1] (.node [11,11,10,9,9,4,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,9,9,5,1,1,1,1,1,1,1] .empty .empty)) (.node [11,11,10,10,3,3,2,2,2,2,2,2,2] (.node [11,11,10,10,3,2,2,2,2,2,2,2,2,1] (.node [11,11,10,9,9,6,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,3,3,3,2,2,2,2,1,1,1] .empty .empty))))

def degreeTree62_217 : RowTree := (.node [11,11,10,9,8,6,1,1,1,1,1,1,1] degreeTree62_215 degreeTree62_216)

def degreeTree62_218 : RowTree := (.node [11,11,10,9,7,7,1,1,1,1,1,1,1] degreeTree62_214 degreeTree62_217)

def degreeTree62_219 : RowTree := (.node [11,11,10,9,6,5,2,2,2,2,1,1] degreeTree62_211 degreeTree62_218)

def degreeTree62_220 : RowTree := (.node [11,11,10,9,4,3,3,3,3,2,2,1] degreeTree62_204 degreeTree62_219)

def degreeTree62_221 : RowTree := (.node [11,11,10,10,4,3,3,2,2,2,2,2] (.node [11,11,10,10,4,2,2,2,2,2,2,2,2] (.node [11,11,10,10,3,3,3,3,3,2,1,1,1] (.node [11,11,10,10,3,3,3,3,3,1,1,1,1,1] (.node [11,11,10,10,3,3,3,3,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,10,10,4,2,2,2,2,2,2,2,1,1] (.node [11,11,10,10,3,3,3,3,3,2,2,1] .empty .empty) .empty)) (.node [11,11,10,10,4,3,3,2,2,2,1,1,1,1] (.node [11,11,10,10,4,3,2,2,2,2,2,2,1] (.node [11,11,10,10,4,3,2,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,4,3,3,2,2,2,2,1,1] .empty .empty))) (.node [11,11,10,10,4,4,2,2,2,2,1,1,1,1] (.node [11,11,10,10,4,3,3,3,2,2,2,1] (.node [11,11,10,10,4,3,3,3,2,2,1,1,1] (.node [11,11,10,10,4,3,3,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,4,3,3,3,3,2,1,1] (.node [11,11,10,10,4,3,3,3,3,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,10,4,4,3,2,2,1,1,1,1,1] (.node [11,11,10,10,4,4,2,2,2,2,2,2] (.node [11,11,10,10,4,4,2,2,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,10,10,4,4,3,2,2,2,1,1,1] .empty .empty))))

def degreeTree62_222 : RowTree := (.node [11,11,10,10,5,2,2,2,2,2,2,1,1,1] (.node [11,11,10,10,4,4,4,2,2,1,1,1,1] (.node [11,11,10,10,4,4,3,3,2,2,1,1] (.node [11,11,10,10,4,4,3,3,2,1,1,1,1] (.node [11,11,10,10,4,4,3,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,4,4,4,2,1,1,1,1,1,1] (.node [11,11,10,10,4,4,3,3,3,1,1,1] .empty .empty) .empty)) (.node [11,11,10,10,4,4,4,3,2,1,1,1] (.node [11,11,10,10,4,4,4,3,1,1,1,1,1] (.node [11,11,10,10,4,4,4,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,10,10,4,4,4,4,1,1,1,1] .empty .empty))) (.node [11,11,10,10,5,3,3,2,2,2,1,1,1] (.node [11,11,10,10,5,3,2,2,2,2,2,1,1] (.node [11,11,10,10,5,3,2,2,2,2,1,1,1,1] (.node [11,11,10,10,5,2,2,2,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,10,10,5,3,3,2,2,1,1,1,1,1] (.node [11,11,10,10,5,3,2,2,2,2,2,2] .empty .empty) .empty)) (.node [11,11,10,10,5,3,3,3,2,1,1,1,1] (.node [11,11,10,10,5,3,3,3,1,1,1,1,1,1] (.node [11,11,10,10,5,3,3,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,10,10,5,3,3,3,2,2,1,1] .empty .empty))))

def degreeTree62_223 : RowTree := (.node [11,11,10,10,4,4,3,2,2,2,2,1] degreeTree62_221 degreeTree62_222)

def degreeTree62_224 : RowTree := (.node [11,11,10,10,5,4,4,2,2,1,1,1] (.node [11,11,10,10,5,4,3,2,2,2,1,1] (.node [11,11,10,10,5,4,2,2,2,2,2,1] (.node [11,11,10,10,5,4,2,2,2,2,1,1,1] (.node [11,11,10,10,5,4,2,2,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,5,4,3,2,2,1,1,1,1] (.node [11,11,10,10,5,4,3,2,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,10,5,4,4,1,1,1,1,1,1,1] (.node [11,11,10,10,5,4,3,3,2,1,1,1] (.node [11,11,10,10,5,4,3,3,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,5,4,4,2,1,1,1,1,1] .empty .empty))) (.node [11,11,10,10,5,5,3,2,1,1,1,1,1] (.node [11,11,10,10,5,5,2,2,2,1,1,1,1] (.node [11,11,10,10,5,5,2,2,1,1,1,1,1,1] (.node [11,11,10,10,5,4,4,3,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,5,5,3,1,1,1,1,1,1,1] (.node [11,11,10,10,5,5,2,2,2,2,1,1] .empty .empty) .empty)) (.node [11,11,10,10,5,5,4,1,1,1,1,1,1] (.node [11,11,10,10,5,5,3,3,1,1,1,1] (.node [11,11,10,10,5,5,3,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,5,5,4,2,1,1,1,1] .empty .empty))))

def degreeTree62_225 : RowTree := (.node [11,11,10,10,6,3,3,3,2,1,1,1] (.node [11,11,10,10,6,3,2,2,2,2,2,1] (.node [11,11,10,10,6,2,2,2,2,2,2,2] (.node [11,11,10,10,6,2,2,2,2,2,2,1,1] (.node [11,11,10,10,6,2,2,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,6,3,2,2,2,2,1,1,1] (.node [11,11,10,10,6,3,2,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,10,6,3,3,2,2,2,1,1] (.node [11,11,10,10,6,3,3,2,2,1,1,1,1] (.node [11,11,10,10,6,3,3,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,6,3,3,3,1,1,1,1,1] .empty .empty))) (.node [11,11,10,10,6,4,3,2,2,1,1,1] (.node [11,11,10,10,6,4,2,2,2,2,1,1] (.node [11,11,10,10,6,4,2,2,2,1,1,1,1] (.node [11,11,10,10,6,4,2,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,6,4,3,2,1,1,1,1,1] (.node [11,11,10,10,6,4,3,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,10,6,4,4,2,1,1,1,1] (.node [11,11,10,10,6,4,4,1,1,1,1,1,1] (.node [11,11,10,10,6,4,3,3,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,6,5,2,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_226 : RowTree := (.node [11,11,10,10,5,5,5,1,1,1,1,1] degreeTree62_224 degreeTree62_225)

def degreeTree62_227 : RowTree := (.node [11,11,10,10,5,3,3,3,3,1,1,1] degreeTree62_223 degreeTree62_226)

def degreeTree62_228 : RowTree := (.node [11,11,10,10,7,2,2,2,2,2,2,1] (.node [11,11,10,10,6,6,2,1,1,1,1,1,1] (.node [11,11,10,10,6,5,3,2,1,1,1,1] (.node [11,11,10,10,6,5,3,1,1,1,1,1,1] (.node [11,11,10,10,6,5,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,6,6,1,1,1,1,1,1,1,1] (.node [11,11,10,10,6,5,4,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,10,7,2,2,2,2,1,1,1,1,1] (.node [11,11,10,10,6,6,3,1,1,1,1,1] (.node [11,11,10,10,6,6,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,7,2,2,2,2,2,1,1,1] .empty .empty))) (.node [11,11,10,10,7,3,3,2,2,1,1,1] (.node [11,11,10,10,7,3,2,2,2,2,1,1] (.node [11,11,10,10,7,3,2,2,2,1,1,1,1] (.node [11,11,10,10,7,3,2,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,7,3,3,2,1,1,1,1,1] (.node [11,11,10,10,7,3,3,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,10,7,4,2,2,1,1,1,1,1] (.node [11,11,10,10,7,4,2,1,1,1,1,1,1,1] (.node [11,11,10,10,7,3,3,3,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,7,4,2,2,2,1,1,1] .empty .empty))))

def degreeTree62_229 : RowTree := (.node [11,11,10,10,8,2,2,2,2,1,1,1,1] (.node [11,11,10,10,7,5,3,1,1,1,1,1] (.node [11,11,10,10,7,5,1,1,1,1,1,1,1,1] (.node [11,11,10,10,7,4,4,1,1,1,1,1] (.node [11,11,10,10,7,4,3,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,7,5,2,2,1,1,1,1] (.node [11,11,10,10,7,5,2,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,10,7,7,1,1,1,1,1,1] (.node [11,11,10,10,7,6,2,1,1,1,1,1] (.node [11,11,10,10,7,6,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,8,2,2,2,1,1,1,1,1,1] .empty .empty))) (.node [11,11,10,10,8,3,3,2,1,1,1,1] (.node [11,11,10,10,8,3,2,2,1,1,1,1,1] (.node [11,11,10,10,8,3,2,1,1,1,1,1,1,1] (.node [11,11,10,10,8,2,2,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,10,10,8,3,3,1,1,1,1,1,1] (.node [11,11,10,10,8,3,2,2,2,1,1,1] .empty .empty) .empty)) (.node [11,11,10,10,8,4,2,2,1,1,1,1] (.node [11,11,10,10,8,4,2,1,1,1,1,1,1] (.node [11,11,10,10,8,4,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,8,4,3,1,1,1,1,1] .empty .empty))))

def degreeTree62_230 : RowTree := (.node [11,11,10,10,7,4,3,1,1,1,1,1,1] degreeTree62_228 degreeTree62_229)

def degreeTree62_231 : RowTree := (.node [11,11,10,10,9,4,2,1,1,1,1,1] (.node [11,11,10,10,9,3,1,1,1,1,1,1,1,1] (.node [11,11,10,10,9,2,2,1,1,1,1,1,1,1] (.node [11,11,10,10,8,6,1,1,1,1,1,1] (.node [11,11,10,10,8,5,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,9,2,2,2,2,1,1,1] (.node [11,11,10,10,9,2,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,10,10,9,3,3,1,1,1,1,1] (.node [11,11,10,10,9,3,2,2,1,1,1,1] (.node [11,11,10,10,9,3,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,9,4,1,1,1,1,1,1,1] .empty .empty))) (.node [11,11,10,10,10,3,2,1,1,1,1,1] (.node [11,11,10,10,10,2,2,1,1,1,1,1,1] (.node [11,11,10,10,10,2,1,1,1,1,1,1,1,1] (.node [11,11,10,10,9,5,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,10,10,10,3,1,1,1,1,1,1,1] (.node [11,11,10,10,10,2,2,2,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,4,4,4,4,4,3,3,3] (.node [11,11,11,4,4,4,4,4,3,2,2,1,1] (.node [11,11,10,10,10,4,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,4,4,4,4,4,4,2,1,1,1] .empty .empty))))

def degreeTree62_232 : RowTree := (.node [11,11,11,5,5,4,3,3,3,3,3] (.node [11,11,11,5,4,4,4,4,3,2,2,1] (.node [11,11,11,5,4,4,4,3,3,3,3] (.node [11,11,11,5,4,4,4,3,3,2,2,1,1] (.node [11,11,11,5,4,4,4,2,2,2,2,2,2] .empty .empty) .empty) (.node [11,11,11,5,4,4,4,4,3,2,1,1,1] (.node [11,11,11,5,4,4,4,4,2,2,2,1,1] .empty .empty) .empty)) (.node [11,11,11,5,5,4,3,2,2,2,2,2,2] (.node [11,11,11,5,4,4,4,4,4,2,1,1] (.node [11,11,11,5,4,4,4,4,4,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,5,5,4,3,3,3,2,2,1,1] .empty .empty))) (.node [11,11,11,5,5,4,4,4,2,2,1,1,1] (.node [11,11,11,5,5,4,4,3,3,2,1,1,1] (.node [11,11,11,5,5,4,4,3,2,2,2,1,1] (.node [11,11,11,5,5,4,4,2,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,11,5,5,4,4,3,3,2,2,1] .empty .empty)) (.node [11,11,11,5,5,4,4,4,3,2,1,1] (.node [11,11,11,5,5,4,4,4,3,1,1,1,1] (.node [11,11,11,5,5,4,4,4,2,2,2,1] .empty .empty) .empty) (.node [11,11,11,5,5,4,4,4,4,1,1,1] .empty .empty))))

def degreeTree62_233 : RowTree := (.node [11,11,11,4,4,4,4,4,4,2,2,1] degreeTree62_231 degreeTree62_232)

def degreeTree62_234 : RowTree := (.node [11,11,10,10,8,5,1,1,1,1,1,1,1] degreeTree62_230 degreeTree62_233)

def degreeTree62_235 : RowTree := (.node [11,11,10,10,6,5,2,2,1,1,1,1,1] degreeTree62_227 degreeTree62_234)

def degreeTree62_236 : RowTree := (.node [11,11,11,5,5,5,4,4,2,1,1,1,1] (.node [11,11,11,5,5,5,4,2,2,2,2,2] (.node [11,11,11,5,5,5,3,3,3,2,1,1,1] (.node [11,11,11,5,5,5,3,3,2,2,2,1,1] (.node [11,11,11,5,5,5,3,2,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,11,5,5,5,4,2,2,2,2,1,1] (.node [11,11,11,5,5,5,3,3,3,2,2,1] .empty .empty) .empty)) (.node [11,11,11,5,5,5,4,3,3,1,1,1,1] (.node [11,11,11,5,5,5,4,3,2,2,2,1] (.node [11,11,11,5,5,5,4,3,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,5,5,5,4,3,3,2,1,1] .empty .empty))) (.node [11,11,11,5,5,5,5,3,2,2,1,1] (.node [11,11,11,5,5,5,5,2,2,2,1,1,1] (.node [11,11,11,5,5,5,4,4,3,1,1,1] (.node [11,11,11,5,5,5,4,4,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,5,5,5,5,3,2,1,1,1,1] (.node [11,11,11,5,5,5,5,2,2,2,2,1] .empty .empty) .empty)) (.node [11,11,11,5,5,5,5,4,2,1,1,1] (.node [11,11,11,5,5,5,5,4,1,1,1,1,1] (.node [11,11,11,5,5,5,5,3,3,1,1,1] .empty .empty) .empty) (.node [11,11,11,5,5,5,5,5,1,1,1,1] .empty .empty))))

def degreeTree62_237 : RowTree := (.node [11,11,11,6,4,4,4,4,2,2,2,1] (.node [11,11,11,6,4,4,4,3,3,1,1,1,1,1] (.node [11,11,11,6,4,4,4,2,2,2,2,1,1,1] (.node [11,11,11,6,4,4,3,3,3,3,3] (.node [11,11,11,6,4,4,3,3,3,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,6,4,4,4,3,2,2,2,1,1] (.node [11,11,11,6,4,4,4,2,2,2,2,2,1] .empty .empty) .empty)) (.node [11,11,11,6,4,4,4,4,2,1,1,1,1,1] (.node [11,11,11,6,4,4,4,3,3,2,2,1] (.node [11,11,11,6,4,4,4,3,3,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,6,4,4,4,4,2,2,1,1,1] .empty .empty))) (.node [11,11,11,6,5,4,2,2,2,2,2,2,2] (.node [11,11,11,6,4,4,4,4,4,1,1,1] (.node [11,11,11,6,4,4,4,4,3,2,1,1] (.node [11,11,11,6,4,4,4,4,3,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,6,5,3,3,3,3,2,2,1,1] (.node [11,11,11,6,5,3,3,2,2,2,2,2,2] .empty .empty) .empty)) (.node [11,11,11,6,5,4,3,3,2,2,2,1,1] (.node [11,11,11,6,5,4,3,2,2,2,2,2,1] (.node [11,11,11,6,5,4,3,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,6,5,4,3,3,3,1,1,1,1,1] .empty .empty))))

def degreeTree62_238 : RowTree := (.node [11,11,11,6,4,4,3,2,2,2,2,2,2] degreeTree62_236 degreeTree62_237)

def degreeTree62_239 : RowTree := (.node [11,11,11,6,5,4,4,4,2,1,1,1,1] (.node [11,11,11,6,5,4,4,3,2,2,1,1,1] (.node [11,11,11,6,5,4,4,2,2,2,2,1,1] (.node [11,11,11,6,5,4,4,2,2,2,1,1,1,1] (.node [11,11,11,6,5,4,3,3,3,2,2,1] .empty .empty) .empty) (.node [11,11,11,6,5,4,4,3,2,1,1,1,1,1] (.node [11,11,11,6,5,4,4,2,2,2,2,2] .empty .empty) .empty)) (.node [11,11,11,6,5,4,4,3,3,2,1,1] (.node [11,11,11,6,5,4,4,3,3,1,1,1,1] (.node [11,11,11,6,5,4,4,3,2,2,2,1] .empty .empty) .empty) (.node [11,11,11,6,5,4,4,4,1,1,1,1,1,1] .empty .empty))) (.node [11,11,11,6,5,5,3,2,2,2,2,1,1] (.node [11,11,11,6,5,5,2,2,2,2,2,1,1,1] (.node [11,11,11,6,5,4,4,4,3,1,1,1] (.node [11,11,11,6,5,4,4,4,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,6,5,5,3,2,2,2,1,1,1,1] (.node [11,11,11,6,5,5,2,2,2,2,2,2,1] .empty .empty) .empty)) (.node [11,11,11,6,5,5,3,3,2,2,1,1,1] (.node [11,11,11,6,5,5,3,3,2,1,1,1,1,1] (.node [11,11,11,6,5,5,3,2,2,2,2,2] .empty .empty) .empty) (.node [11,11,11,6,5,5,3,3,2,2,2,1] .empty .empty))))

def degreeTree62_240 : RowTree := (.node [11,11,11,6,5,5,5,2,1,1,1,1,1,1] (.node [11,11,11,6,5,5,4,3,2,1,1,1,1] (.node [11,11,11,6,5,5,4,2,2,2,1,1,1] (.node [11,11,11,6,5,5,4,2,2,1,1,1,1,1] (.node [11,11,11,6,5,5,3,3,3,2,1,1] .empty .empty) .empty) (.node [11,11,11,6,5,5,4,3,1,1,1,1,1,1] (.node [11,11,11,6,5,5,4,2,2,2,2,1] .empty .empty) .empty)) (.node [11,11,11,6,5,5,4,4,1,1,1,1,1] (.node [11,11,11,6,5,5,4,3,3,1,1,1] (.node [11,11,11,6,5,5,4,3,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,6,5,5,4,4,2,1,1,1] .empty .empty))) (.node [11,11,11,6,6,2,2,2,2,2,2,2,2,1] (.node [11,11,11,6,5,5,5,3,1,1,1,1,1] (.node [11,11,11,6,5,5,5,2,2,2,1,1] (.node [11,11,11,6,5,5,5,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,6,5,5,5,4,1,1,1,1] (.node [11,11,11,6,5,5,5,3,2,1,1,1] .empty .empty) .empty)) (.node [11,11,11,6,6,3,3,2,2,2,2,2,1] (.node [11,11,11,6,6,3,3,2,2,2,2,1,1,1] (.node [11,11,11,6,6,3,2,2,2,2,2,2,2] .empty .empty) .empty) (.node [11,11,11,6,6,3,3,3,2,2,2,1,1] .empty .empty))))

def degreeTree62_241 : RowTree := (.node [11,11,11,6,5,5,3,3,3,1,1,1,1] degreeTree62_239 degreeTree62_240)

def degreeTree62_242 : RowTree := (.node [11,11,11,6,5,4,3,3,3,2,1,1,1] degreeTree62_238 degreeTree62_241)

def degreeTree62_243 : RowTree := (.node [11,11,11,6,6,4,3,3,3,1,1,1,1] (.node [11,11,11,6,6,4,3,2,2,2,2,1,1] (.node [11,11,11,6,6,4,2,2,2,2,2,1,1,1] (.node [11,11,11,6,6,3,3,3,3,2,2,1] (.node [11,11,11,6,6,3,3,3,3,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,6,6,4,3,2,2,2,1,1,1,1] (.node [11,11,11,6,6,4,2,2,2,2,2,2,1] .empty .empty) .empty)) (.node [11,11,11,6,6,4,3,3,2,2,1,1,1] (.node [11,11,11,6,6,4,3,3,2,1,1,1,1,1] (.node [11,11,11,6,6,4,3,2,2,2,2,2] .empty .empty) .empty) (.node [11,11,11,6,6,4,3,3,2,2,2,1] .empty .empty))) (.node [11,11,11,6,6,4,4,3,2,1,1,1,1] (.node [11,11,11,6,6,4,4,2,2,2,1,1,1] (.node [11,11,11,6,6,4,4,2,2,1,1,1,1,1] (.node [11,11,11,6,6,4,3,3,3,2,1,1] .empty .empty) .empty) (.node [11,11,11,6,6,4,4,3,1,1,1,1,1,1] (.node [11,11,11,6,6,4,4,2,2,2,2,1] .empty .empty) .empty)) (.node [11,11,11,6,6,4,4,4,1,1,1,1,1] (.node [11,11,11,6,6,4,4,3,3,1,1,1] (.node [11,11,11,6,6,4,4,3,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,6,6,4,4,4,2,1,1,1] .empty .empty))))

def degreeTree62_244 : RowTree := (.node [11,11,11,6,6,5,4,2,2,1,1,1,1] (.node [11,11,11,6,6,5,3,3,1,1,1,1,1,1] (.node [11,11,11,6,6,5,3,2,2,1,1,1,1,1] (.node [11,11,11,6,6,5,2,2,2,2,2,2] (.node [11,11,11,6,6,5,2,2,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,6,6,5,3,2,2,2,2,1] (.node [11,11,11,6,6,5,3,2,2,2,1,1,1] .empty .empty) .empty)) (.node [11,11,11,6,6,5,3,3,3,1,1,1] (.node [11,11,11,6,6,5,3,3,2,2,1,1] (.node [11,11,11,6,6,5,3,3,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,6,6,5,4,2,1,1,1,1,1,1] .empty .empty))) (.node [11,11,11,6,6,5,5,2,1,1,1,1,1] (.node [11,11,11,6,6,5,4,3,2,1,1,1] (.node [11,11,11,6,6,5,4,3,1,1,1,1,1] (.node [11,11,11,6,6,5,4,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,6,6,5,5,1,1,1,1,1,1,1] (.node [11,11,11,6,6,5,4,4,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,6,6,6,2,2,2,1,1,1,1,1] (.node [11,11,11,6,6,5,5,3,1,1,1,1] (.node [11,11,11,6,6,5,5,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,6,6,6,2,2,2,2,1,1,1] .empty .empty))))

def degreeTree62_245 : RowTree := (.node [11,11,11,6,6,5,2,2,2,2,1,1,1,1] degreeTree62_243 degreeTree62_244)

def degreeTree62_246 : RowTree := (.node [11,11,11,6,6,6,5,2,1,1,1,1] (.node [11,11,11,6,6,6,4,1,1,1,1,1,1,1] (.node [11,11,11,6,6,6,3,2,2,2,1,1] (.node [11,11,11,6,6,6,3,2,2,1,1,1,1] (.node [11,11,11,6,6,6,3,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,6,6,6,3,3,2,1,1,1] (.node [11,11,11,6,6,6,3,3,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,6,6,6,4,3,1,1,1,1] (.node [11,11,11,6,6,6,4,2,2,1,1,1] (.node [11,11,11,6,6,6,4,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,6,6,6,5,1,1,1,1,1,1] .empty .empty))) (.node [11,11,11,7,4,4,3,2,2,2,2,2,1] (.node [11,11,11,7,4,3,3,3,3,2,2,1,1] (.node [11,11,11,7,4,3,3,2,2,2,2,2,2] (.node [11,11,11,6,6,6,6,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,4,4,3,2,2,2,2,1,1,1] (.node [11,11,11,7,4,4,2,2,2,2,2,2,2] .empty .empty) .empty)) (.node [11,11,11,7,4,4,3,3,3,2,1,1,1] (.node [11,11,11,7,4,4,3,3,3,1,1,1,1,1] (.node [11,11,11,7,4,4,3,3,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,7,4,4,3,3,3,2,2,1] .empty .empty))))

def degreeTree62_247 : RowTree := (.node [11,11,11,7,4,4,4,4,3,1,1,1] (.node [11,11,11,7,4,4,4,3,3,1,1,1,1] (.node [11,11,11,7,4,4,4,3,2,1,1,1,1,1] (.node [11,11,11,7,4,4,4,2,2,2,2,2] (.node [11,11,11,7,4,4,4,2,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,7,4,4,4,3,2,2,2,1] (.node [11,11,11,7,4,4,4,3,2,2,1,1,1] .empty .empty) .empty)) (.node [11,11,11,7,4,4,4,4,2,1,1,1,1] (.node [11,11,11,7,4,4,4,4,1,1,1,1,1,1] (.node [11,11,11,7,4,4,4,3,3,2,1,1] .empty .empty) .empty) (.node [11,11,11,7,4,4,4,4,2,2,1,1] .empty .empty))) (.node [11,11,11,7,5,3,3,3,2,2,2,1,1] (.node [11,11,11,7,5,3,3,2,2,2,2,1,1,1] (.node [11,11,11,7,5,3,2,2,2,2,2,2,2] (.node [11,11,11,7,5,2,2,2,2,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,11,7,5,3,3,2,2,2,2,2,1] .empty .empty)) (.node [11,11,11,7,5,3,3,3,3,2,2,1] (.node [11,11,11,7,5,3,3,3,3,2,1,1,1] (.node [11,11,11,7,5,3,3,3,3,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,5,4,2,2,2,2,2,1,1,1] .empty .empty))))

def degreeTree62_248 : RowTree := (.node [11,11,11,7,4,4,4,2,2,2,1,1,1,1] degreeTree62_246 degreeTree62_247)

def degreeTree62_249 : RowTree := (.node [11,11,11,6,6,6,2,2,2,2,2,1] degreeTree62_245 degreeTree62_248)

def degreeTree62_250 : RowTree := (.node [11,11,11,6,6,3,3,3,3,1,1,1,1,1] degreeTree62_242 degreeTree62_249)

def degreeTree62_251 : RowTree := (.node [11,11,11,5,5,5,2,2,2,2,2,2,2] degreeTree62_235 degreeTree62_250)

def degreeTree62_252 : RowTree := (.node [11,11,10,10,3,3,3,2,2,2,2,2,1] degreeTree62_220 degreeTree62_251)

def degreeTree62_255 : RowTree := (.node [11,11,11,7,5,4,4,2,2,2,2,1] (.node [11,11,11,7,5,4,3,3,2,2,2,1] (.node [11,11,11,7,5,4,3,2,2,2,2,2] (.node [11,11,11,7,5,4,3,2,2,2,2,1,1] (.node [11,11,11,7,5,4,3,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,5,4,3,3,2,2,1,1,1] (.node [11,11,11,7,5,4,3,3,2,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,7,5,4,4,2,2,1,1,1,1,1] (.node [11,11,11,7,5,4,3,3,3,2,1,1] (.node [11,11,11,7,5,4,3,3,3,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,5,4,4,2,2,2,1,1,1] .empty .empty))) (.node [11,11,11,7,5,4,4,4,2,1,1,1] (.node [11,11,11,7,5,4,4,3,2,2,1,1] (.node [11,11,11,7,5,4,4,3,2,1,1,1,1] (.node [11,11,11,7,5,4,4,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,5,4,4,4,1,1,1,1,1] (.node [11,11,11,7,5,4,4,3,3,1,1,1] .empty .empty) .empty)) (.node [11,11,11,7,5,5,2,2,2,2,2,2] (.node [11,11,11,7,5,5,2,2,2,2,2,1,1] (.node [11,11,11,7,5,5,2,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,5,5,3,2,2,1,1,1,1,1] .empty .empty))))

def degreeTree62_256 : RowTree := (.node [11,11,11,7,5,5,4,4,1,1,1,1] (.node [11,11,11,7,5,5,4,2,1,1,1,1,1,1] (.node [11,11,11,7,5,5,3,3,2,1,1,1,1] (.node [11,11,11,7,5,5,3,3,1,1,1,1,1,1] (.node [11,11,11,7,5,5,3,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,11,7,5,5,3,3,3,1,1,1] (.node [11,11,11,7,5,5,3,3,2,2,1,1] .empty .empty) .empty)) (.node [11,11,11,7,5,5,4,3,1,1,1,1,1] (.node [11,11,11,7,5,5,4,2,2,2,1,1] (.node [11,11,11,7,5,5,4,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,5,5,4,3,2,1,1,1] .empty .empty))) (.node [11,11,11,7,6,2,2,2,2,2,2,2,2] (.node [11,11,11,7,5,5,5,2,2,1,1,1] (.node [11,11,11,7,5,5,5,2,1,1,1,1,1] (.node [11,11,11,7,5,5,5,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,6,2,2,2,2,2,2,2,1,1] (.node [11,11,11,7,5,5,5,3,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,7,6,3,3,2,2,2,1,1,1,1] (.node [11,11,11,7,6,3,2,2,2,2,2,2,1] (.node [11,11,11,7,6,3,2,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,6,3,3,2,2,2,2,1,1] .empty .empty))))

def degreeTree62_257 : RowTree := (.node [11,11,11,7,5,5,3,2,2,2,1,1,1] degreeTree62_255 degreeTree62_256)

def degreeTree62_258 : RowTree := (.node [11,11,11,7,6,4,3,2,2,2,2,1] (.node [11,11,11,7,6,4,2,2,2,2,1,1,1,1] (.node [11,11,11,7,6,3,3,3,2,2,2,1] (.node [11,11,11,7,6,3,3,3,2,2,1,1,1] (.node [11,11,11,7,6,3,3,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,6,3,3,3,3,2,1,1] (.node [11,11,11,7,6,3,3,3,3,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,7,6,4,3,2,2,1,1,1,1,1] (.node [11,11,11,7,6,4,2,2,2,2,2,2] (.node [11,11,11,7,6,4,2,2,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,7,6,4,3,2,2,2,1,1,1] .empty .empty))) (.node [11,11,11,7,6,4,4,2,2,1,1,1,1] (.node [11,11,11,7,6,4,3,3,2,2,1,1] (.node [11,11,11,7,6,4,3,3,2,1,1,1,1] (.node [11,11,11,7,6,4,3,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,6,4,4,2,1,1,1,1,1,1] (.node [11,11,11,7,6,4,3,3,3,1,1,1] .empty .empty) .empty)) (.node [11,11,11,7,6,4,4,3,2,1,1,1] (.node [11,11,11,7,6,4,4,3,1,1,1,1,1] (.node [11,11,11,7,6,4,4,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,7,6,4,4,4,1,1,1,1] .empty .empty))))

def degreeTree62_259 : RowTree := (.node [11,11,11,7,6,5,4,3,1,1,1,1] (.node [11,11,11,7,6,5,3,3,1,1,1,1,1] (.node [11,11,11,7,6,5,3,2,1,1,1,1,1,1] (.node [11,11,11,7,6,5,2,2,2,2,2,1] (.node [11,11,11,7,6,5,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,6,5,3,2,2,2,1,1] (.node [11,11,11,7,6,5,3,2,2,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,7,6,5,4,2,1,1,1,1,1] (.node [11,11,11,7,6,5,4,1,1,1,1,1,1,1] (.node [11,11,11,7,6,5,3,3,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,6,5,4,2,2,1,1,1] .empty .empty))) (.node [11,11,11,7,6,6,3,1,1,1,1,1,1,1] (.node [11,11,11,7,6,6,2,2,1,1,1,1,1,1] (.node [11,11,11,7,6,5,5,2,1,1,1,1] (.node [11,11,11,7,6,5,5,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,6,6,2,2,2,2,1,1] (.node [11,11,11,7,6,6,2,2,2,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,7,6,6,3,3,1,1,1,1] (.node [11,11,11,7,6,6,3,2,2,1,1,1] (.node [11,11,11,7,6,6,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,6,6,4,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_260 : RowTree := (.node [11,11,11,7,6,5,2,2,2,1,1,1,1,1] degreeTree62_258 degreeTree62_259)

def degreeTree62_261 : RowTree := (.node [11,11,11,7,6,3,3,2,2,2,2,2] degreeTree62_257 degreeTree62_260)

def degreeTree62_262 : RowTree := (.node [11,11,11,7,7,3,3,3,2,1,1,1,1] (.node [11,11,11,7,7,3,2,2,2,2,2,2] (.node [11,11,11,7,7,2,2,2,2,2,2,2,1] (.node [11,11,11,7,7,2,2,2,2,2,2,1,1,1] (.node [11,11,11,7,6,6,5,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,7,3,2,2,2,2,2,1,1] (.node [11,11,11,7,7,3,2,2,2,2,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,7,7,3,3,2,2,2,2,1] (.node [11,11,11,7,7,3,3,2,2,2,1,1,1] (.node [11,11,11,7,7,3,3,2,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,7,3,3,3,1,1,1,1,1,1] .empty .empty))) (.node [11,11,11,7,7,4,3,2,1,1,1,1,1,1] (.node [11,11,11,7,7,4,2,2,2,1,1,1,1,1] (.node [11,11,11,7,7,3,3,3,3,1,1,1] (.node [11,11,11,7,7,3,3,3,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,7,7,4,2,2,2,2,2,1] (.node [11,11,11,7,7,4,2,2,2,2,1,1,1] .empty .empty) .empty)) (.node [11,11,11,7,7,4,3,3,1,1,1,1,1] (.node [11,11,11,7,7,4,3,2,2,2,1,1] (.node [11,11,11,7,7,4,3,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,7,4,3,3,2,1,1,1] .empty .empty))))

def degreeTree62_263 : RowTree := (.node [11,11,11,7,7,5,4,1,1,1,1,1,1] (.node [11,11,11,7,7,5,2,2,2,2,1,1] (.node [11,11,11,7,7,4,4,3,1,1,1,1] (.node [11,11,11,7,7,4,4,2,2,1,1,1] (.node [11,11,11,7,7,4,4,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,7,5,2,2,2,1,1,1,1] (.node [11,11,11,7,7,5,2,2,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,7,7,5,3,2,2,1,1,1] (.node [11,11,11,7,7,5,3,2,1,1,1,1,1] (.node [11,11,11,7,7,5,3,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,7,5,3,3,1,1,1,1] .empty .empty))) (.node [11,11,11,7,7,6,3,1,1,1,1,1,1] (.node [11,11,11,7,7,6,2,1,1,1,1,1,1,1] (.node [11,11,11,7,7,5,5,1,1,1,1,1] (.node [11,11,11,7,7,5,4,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,7,6,2,2,2,1,1,1] (.node [11,11,11,7,7,6,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,7,7,7,1,1,1,1,1,1,1,1] (.node [11,11,11,7,7,6,4,1,1,1,1,1] (.node [11,11,11,7,7,6,3,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,7,7,7,2,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_264 : RowTree := (.node [11,11,11,7,7,4,4,1,1,1,1,1,1,1] degreeTree62_262 degreeTree62_263)

def degreeTree62_265 : RowTree := (.node [11,11,11,8,4,3,3,3,3,2,2,1] (.node [11,11,11,8,4,3,3,2,2,2,2,1,1,1] (.node [11,11,11,8,3,3,3,3,3,2,2,1,1] (.node [11,11,11,8,3,3,3,2,2,2,2,2,2] (.node [11,11,11,7,7,7,3,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,4,3,2,2,2,2,2,2,2] (.node [11,11,11,8,4,2,2,2,2,2,2,2,2,1] .empty .empty) .empty)) (.node [11,11,11,8,4,3,3,3,3,1,1,1,1,1] (.node [11,11,11,8,4,3,3,3,2,2,2,1,1] (.node [11,11,11,8,4,3,3,2,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,11,8,4,3,3,3,3,2,1,1,1] .empty .empty))) (.node [11,11,11,8,4,4,3,3,2,1,1,1,1,1] (.node [11,11,11,8,4,4,3,2,2,2,1,1,1,1] (.node [11,11,11,8,4,4,2,2,2,2,2,2,1] (.node [11,11,11,8,4,4,2,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,4,4,3,2,2,2,2,2] (.node [11,11,11,8,4,4,3,2,2,2,2,1,1] .empty .empty) .empty)) (.node [11,11,11,8,4,4,3,3,3,1,1,1,1] (.node [11,11,11,8,4,4,3,3,2,2,2,1] (.node [11,11,11,8,4,4,3,3,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,4,4,3,3,3,2,1,1] .empty .empty))))

def degreeTree62_266 : RowTree := (.node [11,11,11,8,5,3,2,2,2,2,2,1,1,1] (.node [11,11,11,8,4,4,4,3,3,1,1,1] (.node [11,11,11,8,4,4,4,3,1,1,1,1,1,1] (.node [11,11,11,8,4,4,4,2,2,2,2,1] (.node [11,11,11,8,4,4,4,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,4,4,4,3,2,2,1,1] (.node [11,11,11,8,4,4,4,3,2,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,8,5,2,2,2,2,2,2,2,1,1] (.node [11,11,11,8,4,4,4,4,2,1,1,1] (.node [11,11,11,8,4,4,4,4,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,5,2,2,2,2,2,2,2,2] .empty .empty))) (.node [11,11,11,8,5,3,3,3,2,2,1,1,1] (.node [11,11,11,8,5,3,3,2,2,2,2,1,1] (.node [11,11,11,8,5,3,3,2,2,2,1,1,1,1] (.node [11,11,11,8,5,3,2,2,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,11,8,5,3,3,3,2,1,1,1,1,1] (.node [11,11,11,8,5,3,3,2,2,2,2,2] .empty .empty) .empty)) (.node [11,11,11,8,5,3,3,3,3,2,1,1] (.node [11,11,11,8,5,3,3,3,3,1,1,1,1] (.node [11,11,11,8,5,3,3,3,2,2,2,1] .empty .empty) .empty) (.node [11,11,11,8,5,4,2,2,2,2,1,1,1,1] .empty .empty))))

def degreeTree62_267 : RowTree := (.node [11,11,11,8,4,4,4,2,2,1,1,1,1,1] degreeTree62_265 degreeTree62_266)

def degreeTree62_268 : RowTree := (.node [11,11,11,7,7,7,2,2,1,1,1,1] degreeTree62_264 degreeTree62_267)

def degreeTree62_269 : RowTree := (.node [11,11,11,7,6,6,4,2,1,1,1,1] degreeTree62_261 degreeTree62_268)

def degreeTree62_270 : RowTree := (.node [11,11,11,8,5,4,4,2,2,2,1,1] (.node [11,11,11,8,5,4,3,3,2,1,1,1,1] (.node [11,11,11,8,5,4,3,2,2,2,1,1,1] (.node [11,11,11,8,5,4,3,2,2,1,1,1,1,1] (.node [11,11,11,8,5,4,2,2,2,2,2,2] .empty .empty) .empty) (.node [11,11,11,8,5,4,3,3,1,1,1,1,1,1] (.node [11,11,11,8,5,4,3,2,2,2,2,1] .empty .empty) .empty)) (.node [11,11,11,8,5,4,4,2,1,1,1,1,1,1] (.node [11,11,11,8,5,4,3,3,3,1,1,1] (.node [11,11,11,8,5,4,3,3,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,8,5,4,4,2,2,1,1,1,1] .empty .empty))) (.node [11,11,11,8,5,5,2,2,2,2,2,1] (.node [11,11,11,8,5,4,4,4,1,1,1,1] (.node [11,11,11,8,5,4,4,3,2,1,1,1] (.node [11,11,11,8,5,4,4,3,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,5,5,2,2,2,2,1,1,1] (.node [11,11,11,8,5,5,2,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,8,5,5,3,2,2,2,1,1] (.node [11,11,11,8,5,5,3,2,2,1,1,1,1] (.node [11,11,11,8,5,5,3,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,5,5,3,3,1,1,1,1,1] .empty .empty))))

def degreeTree62_271 : RowTree := (.node [11,11,11,8,6,3,2,2,2,2,2,2] (.node [11,11,11,8,5,5,5,2,1,1,1,1] (.node [11,11,11,8,5,5,4,2,2,1,1,1] (.node [11,11,11,8,5,5,4,2,1,1,1,1,1] (.node [11,11,11,8,5,5,4,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,5,5,5,1,1,1,1,1,1] (.node [11,11,11,8,5,5,4,3,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,8,6,3,2,2,2,2,1,1,1,1] (.node [11,11,11,8,6,2,2,2,2,2,2,2,1] (.node [11,11,11,8,6,2,2,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,6,3,2,2,2,2,2,1,1] .empty .empty))) (.node [11,11,11,8,6,3,3,3,2,2,1,1] (.node [11,11,11,8,6,3,3,2,2,2,2,1] (.node [11,11,11,8,6,3,3,2,2,2,1,1,1] (.node [11,11,11,8,6,3,3,2,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,6,3,3,3,2,1,1,1,1] (.node [11,11,11,8,6,3,3,3,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,8,6,4,2,2,2,2,1,1,1] (.node [11,11,11,8,6,4,2,2,2,1,1,1,1,1] (.node [11,11,11,8,6,3,3,3,3,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,6,4,2,2,2,2,2,1] .empty .empty))))

def degreeTree62_272 : RowTree := (.node [11,11,11,8,5,5,3,3,2,1,1,1] degreeTree62_270 degreeTree62_271)

def degreeTree62_273 : RowTree := (.node [11,11,11,8,6,5,2,2,2,2,1,1] (.node [11,11,11,8,6,4,4,2,1,1,1,1,1] (.node [11,11,11,8,6,4,3,3,1,1,1,1,1] (.node [11,11,11,8,6,4,3,2,2,2,1,1] (.node [11,11,11,8,6,4,3,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,6,4,4,1,1,1,1,1,1,1] (.node [11,11,11,8,6,4,3,3,2,1,1,1] .empty .empty) .empty)) (.node [11,11,11,8,6,5,2,2,1,1,1,1,1,1] (.node [11,11,11,8,6,4,4,3,1,1,1,1] (.node [11,11,11,8,6,4,4,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,6,5,2,2,2,1,1,1,1] .empty .empty))) (.node [11,11,11,8,6,5,4,2,1,1,1,1] (.node [11,11,11,8,6,5,3,2,2,1,1,1] (.node [11,11,11,8,6,5,3,2,1,1,1,1,1] (.node [11,11,11,8,6,5,3,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,6,5,4,1,1,1,1,1,1] (.node [11,11,11,8,6,5,3,3,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,8,6,6,2,2,1,1,1,1,1] (.node [11,11,11,8,6,6,2,1,1,1,1,1,1,1] (.node [11,11,11,8,6,5,5,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,6,6,2,2,2,1,1,1] .empty .empty))))

def degreeTree62_274 : RowTree := (.node [11,11,11,8,7,3,3,2,2,2,1,1] (.node [11,11,11,8,7,3,2,2,2,1,1,1,1,1] (.node [11,11,11,8,7,2,2,2,2,2,1,1,1,1] (.node [11,11,11,8,6,6,4,1,1,1,1,1] (.node [11,11,11,8,6,6,3,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,7,2,2,2,2,2,2,2] (.node [11,11,11,8,7,2,2,2,2,2,2,1,1] .empty .empty) .empty)) (.node [11,11,11,8,7,3,3,2,1,1,1,1,1,1] (.node [11,11,11,8,7,3,2,2,2,2,2,1] (.node [11,11,11,8,7,3,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,7,3,3,2,2,1,1,1,1] .empty .empty))) (.node [11,11,11,8,7,4,3,1,1,1,1,1,1,1] (.node [11,11,11,8,7,4,2,2,1,1,1,1,1,1] (.node [11,11,11,8,7,3,3,3,2,1,1,1] (.node [11,11,11,8,7,3,3,3,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,7,4,2,2,2,2,1,1] (.node [11,11,11,8,7,4,2,2,2,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,8,7,4,3,3,1,1,1,1] (.node [11,11,11,8,7,4,3,2,2,1,1,1] (.node [11,11,11,8,7,4,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,7,4,4,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_275 : RowTree := (.node [11,11,11,8,6,6,3,1,1,1,1,1,1] degreeTree62_273 degreeTree62_274)

def degreeTree62_276 : RowTree := (.node [11,11,11,8,6,4,3,2,1,1,1,1,1,1] degreeTree62_272 degreeTree62_275)

def degreeTree62_277 : RowTree := (.node [11,11,11,8,7,7,1,1,1,1,1,1,1] (.node [11,11,11,8,7,5,4,1,1,1,1,1] (.node [11,11,11,8,7,5,2,2,2,1,1,1] (.node [11,11,11,8,7,5,2,2,1,1,1,1,1] (.node [11,11,11,8,7,5,2,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,7,5,3,2,1,1,1,1] (.node [11,11,11,8,7,5,3,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,8,7,6,2,2,1,1,1,1] (.node [11,11,11,8,7,6,2,1,1,1,1,1,1] (.node [11,11,11,8,7,6,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,7,6,3,1,1,1,1,1] .empty .empty))) (.node [11,11,11,8,8,3,2,2,2,1,1,1,1] (.node [11,11,11,8,8,2,2,2,2,2,1,1,1] (.node [11,11,11,8,8,2,2,2,2,1,1,1,1,1] (.node [11,11,11,8,7,7,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,8,3,2,2,1,1,1,1,1,1] (.node [11,11,11,8,8,2,2,2,2,2,2,1] .empty .empty) .empty)) (.node [11,11,11,8,8,3,3,2,1,1,1,1,1] (.node [11,11,11,8,8,3,3,1,1,1,1,1,1,1] (.node [11,11,11,8,8,3,2,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,8,8,3,3,2,2,1,1,1] .empty .empty))))

def degreeTree62_278 : RowTree := (.node [11,11,11,8,8,6,1,1,1,1,1,1,1] (.node [11,11,11,8,8,4,4,1,1,1,1,1] (.node [11,11,11,8,8,4,2,2,2,1,1,1] (.node [11,11,11,8,8,4,2,2,1,1,1,1,1] (.node [11,11,11,8,8,4,2,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,8,4,3,2,1,1,1,1] (.node [11,11,11,8,8,4,3,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,8,8,5,2,2,1,1,1,1] (.node [11,11,11,8,8,5,2,1,1,1,1,1,1] (.node [11,11,11,8,8,5,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,8,8,5,3,1,1,1,1,1] .empty .empty))) (.node [11,11,11,9,3,3,3,2,2,2,2,2,1] (.node [11,11,11,9,3,2,2,2,2,2,2,2,2,1] (.node [11,11,11,8,8,7,1,1,1,1,1,1] (.node [11,11,11,8,8,6,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,3,3,3,2,2,2,2,1,1,1] (.node [11,11,11,9,3,3,2,2,2,2,2,2,2] .empty .empty) .empty)) (.node [11,11,11,9,3,3,3,3,3,2,1,1,1] (.node [11,11,11,9,3,3,3,3,3,1,1,1,1,1] (.node [11,11,11,9,3,3,3,3,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,9,3,3,3,3,3,2,2,1] .empty .empty))))

def degreeTree62_279 : RowTree := (.node [11,11,11,8,8,3,3,3,1,1,1,1] degreeTree62_277 degreeTree62_278)

def degreeTree62_280 : RowTree := (.node [11,11,11,9,4,3,3,3,3,2,1,1] (.node [11,11,11,9,4,3,3,2,2,2,2,2] (.node [11,11,11,9,4,3,2,2,2,2,2,2,1] (.node [11,11,11,9,4,3,2,2,2,2,2,1,1,1] (.node [11,11,11,9,4,2,2,2,2,2,2,2,2] .empty .empty) .empty) (.node [11,11,11,9,4,3,3,2,2,2,2,1,1] (.node [11,11,11,9,4,3,3,2,2,2,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,9,4,3,3,3,2,2,2,1] (.node [11,11,11,9,4,3,3,3,2,2,1,1,1] (.node [11,11,11,9,4,3,3,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,4,3,3,3,3,1,1,1,1] .empty .empty))) (.node [11,11,11,9,4,4,3,2,2,2,2,1] (.node [11,11,11,9,4,4,2,2,2,2,2,2] (.node [11,11,11,9,4,4,2,2,2,2,2,1,1] (.node [11,11,11,9,4,4,2,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,4,4,3,2,2,2,1,1,1] (.node [11,11,11,9,4,4,3,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,9,4,4,3,3,2,2,1,1] (.node [11,11,11,9,4,4,3,3,2,1,1,1,1] (.node [11,11,11,9,4,4,3,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,4,4,3,3,3,1,1,1] .empty .empty))))

def degreeTree62_281 : RowTree := (.node [11,11,11,9,5,3,3,2,2,1,1,1,1,1] (.node [11,11,11,9,5,2,2,2,2,2,2,1,1,1] (.node [11,11,11,9,4,4,4,3,1,1,1,1,1] (.node [11,11,11,9,4,4,4,2,2,2,1,1] (.node [11,11,11,9,4,4,4,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,4,4,4,4,1,1,1,1] (.node [11,11,11,9,4,4,4,3,2,1,1,1] .empty .empty) .empty)) (.node [11,11,11,9,5,3,2,2,2,2,2,1,1] (.node [11,11,11,9,5,3,2,2,2,2,1,1,1,1] (.node [11,11,11,9,5,2,2,2,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,11,9,5,3,2,2,2,2,2,2] .empty .empty))) (.node [11,11,11,9,5,3,3,3,2,2,1,1] (.node [11,11,11,9,5,3,3,3,1,1,1,1,1,1] (.node [11,11,11,9,5,3,3,2,2,2,2,1] (.node [11,11,11,9,5,3,3,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,5,3,3,3,2,1,1,1,1] .empty .empty)) (.node [11,11,11,9,5,4,2,2,2,2,1,1,1] (.node [11,11,11,9,5,4,2,2,2,1,1,1,1,1] (.node [11,11,11,9,5,3,3,3,3,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,5,4,2,2,2,2,2,1] .empty .empty))))

def degreeTree62_282 : RowTree := (.node [11,11,11,9,4,4,4,2,1,1,1,1,1,1] degreeTree62_280 degreeTree62_281)

def degreeTree62_283 : RowTree := (.node [11,11,11,9,4,2,2,2,2,2,2,2,1,1] degreeTree62_279 degreeTree62_282)

def degreeTree62_284 : RowTree := (.node [11,11,11,8,7,4,4,2,1,1,1,1] degreeTree62_276 degreeTree62_283)

def degreeTree62_285 : RowTree := (.node [11,11,11,8,5,4,2,2,2,2,2,1,1] degreeTree62_269 degreeTree62_284)

def degreeTree62_286 : RowTree := (.node [11,11,11,9,5,5,2,2,2,2,1,1] (.node [11,11,11,9,5,4,4,2,1,1,1,1,1] (.node [11,11,11,9,5,4,3,3,1,1,1,1,1] (.node [11,11,11,9,5,4,3,2,2,2,1,1] (.node [11,11,11,9,5,4,3,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,5,4,4,1,1,1,1,1,1,1] (.node [11,11,11,9,5,4,3,3,2,1,1,1] .empty .empty) .empty)) (.node [11,11,11,9,5,5,2,2,1,1,1,1,1,1] (.node [11,11,11,9,5,4,4,3,1,1,1,1] (.node [11,11,11,9,5,4,4,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,5,5,2,2,2,1,1,1,1] .empty .empty))) (.node [11,11,11,9,5,5,4,2,1,1,1,1] (.node [11,11,11,9,5,5,3,2,2,1,1,1] (.node [11,11,11,9,5,5,3,2,1,1,1,1,1] (.node [11,11,11,9,5,5,3,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,5,5,4,1,1,1,1,1,1] (.node [11,11,11,9,5,5,3,3,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,9,6,2,2,2,2,2,2,1,1] (.node [11,11,11,9,6,2,2,2,2,2,1,1,1,1] (.node [11,11,11,9,5,5,5,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,6,2,2,2,2,2,2,2] .empty .empty))))

def degreeTree62_287 : RowTree := (.node [11,11,11,9,6,4,3,1,1,1,1,1,1,1] (.node [11,11,11,9,6,3,3,3,1,1,1,1,1] (.node [11,11,11,9,6,3,3,2,1,1,1,1,1,1] (.node [11,11,11,9,6,3,2,2,2,2,2,1] (.node [11,11,11,9,6,3,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,6,3,3,2,2,2,1,1] (.node [11,11,11,9,6,3,3,2,2,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,9,6,4,2,2,2,1,1,1,1] (.node [11,11,11,9,6,4,2,2,1,1,1,1,1,1] (.node [11,11,11,9,6,3,3,3,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,6,4,2,2,2,2,1,1] .empty .empty))) (.node [11,11,11,9,6,5,2,1,1,1,1,1,1,1] (.node [11,11,11,9,6,4,3,3,1,1,1,1] (.node [11,11,11,9,6,4,3,2,2,1,1,1] (.node [11,11,11,9,6,4,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,6,4,4,2,1,1,1,1] (.node [11,11,11,9,6,4,4,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,9,6,5,3,1,1,1,1,1,1] (.node [11,11,11,9,6,5,2,2,2,1,1,1] (.node [11,11,11,9,6,5,2,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,6,5,3,2,1,1,1,1] .empty .empty))))

def degreeTree62_288 : RowTree := (.node [11,11,11,9,6,3,2,2,2,1,1,1,1,1] degreeTree62_286 degreeTree62_287)

def degreeTree62_289 : RowTree := (.node [11,11,11,9,7,3,3,1,1,1,1,1,1,1] (.node [11,11,11,9,7,2,2,2,2,2,1,1,1] (.node [11,11,11,9,6,6,2,2,1,1,1,1] (.node [11,11,11,9,6,6,2,1,1,1,1,1,1] (.node [11,11,11,9,6,6,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,7,2,2,2,2,1,1,1,1,1] (.node [11,11,11,9,6,6,3,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,9,7,3,2,2,2,1,1,1,1] (.node [11,11,11,9,7,3,2,2,1,1,1,1,1,1] (.node [11,11,11,9,7,2,2,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,11,9,7,3,2,2,2,2,1,1] .empty .empty))) (.node [11,11,11,9,7,4,2,2,2,1,1,1] (.node [11,11,11,9,7,3,3,3,1,1,1,1] (.node [11,11,11,9,7,3,3,2,2,1,1,1] (.node [11,11,11,9,7,3,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,7,4,2,2,1,1,1,1,1] (.node [11,11,11,9,7,4,2,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,9,7,4,4,1,1,1,1,1] (.node [11,11,11,9,7,4,3,2,1,1,1,1] (.node [11,11,11,9,7,4,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,7,5,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_290 : RowTree := (.node [11,11,11,9,8,3,2,2,2,1,1,1] (.node [11,11,11,9,8,2,2,2,1,1,1,1,1,1] (.node [11,11,11,9,7,6,1,1,1,1,1,1,1] (.node [11,11,11,9,7,5,3,1,1,1,1,1] (.node [11,11,11,9,7,5,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,7,7,1,1,1,1,1,1] (.node [11,11,11,9,7,6,2,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,9,8,3,2,1,1,1,1,1,1,1] (.node [11,11,11,9,8,2,2,2,2,2,1,1] (.node [11,11,11,9,8,2,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,8,3,2,2,1,1,1,1,1] .empty .empty))) (.node [11,11,11,9,8,4,3,1,1,1,1,1] (.node [11,11,11,9,8,4,1,1,1,1,1,1,1,1] (.node [11,11,11,9,8,3,3,2,1,1,1,1] (.node [11,11,11,9,8,3,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,8,4,2,2,1,1,1,1] (.node [11,11,11,9,8,4,2,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,9,8,6,1,1,1,1,1,1] (.node [11,11,11,9,8,5,2,1,1,1,1,1] (.node [11,11,11,9,8,5,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,9,2,2,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_291 : RowTree := (.node [11,11,11,9,7,5,2,1,1,1,1,1,1] degreeTree62_289 degreeTree62_290)

def degreeTree62_292 : RowTree := (.node [11,11,11,9,6,5,4,1,1,1,1,1] degreeTree62_288 degreeTree62_291)

def degreeTree62_293 : RowTree := (.node [11,11,11,10,3,2,2,2,2,2,2,2,2] (.node [11,11,11,9,9,4,1,1,1,1,1,1,1] (.node [11,11,11,9,9,3,2,1,1,1,1,1,1] (.node [11,11,11,9,9,3,1,1,1,1,1,1,1,1] (.node [11,11,11,9,9,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,9,9,3,3,1,1,1,1,1] (.node [11,11,11,9,9,3,2,2,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,10,2,2,2,2,2,2,2,2,2,1] (.node [11,11,11,9,9,5,1,1,1,1,1,1] (.node [11,11,11,9,9,4,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,3,2,2,2,2,2,2,2,1,1] .empty .empty))) (.node [11,11,11,10,3,3,3,3,2,1,1,1,1,1] (.node [11,11,11,10,3,3,3,2,2,2,1,1,1,1] (.node [11,11,11,10,3,3,2,2,2,2,2,2,1] (.node [11,11,11,10,3,3,2,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,3,3,3,2,2,2,2,2] (.node [11,11,11,10,3,3,3,2,2,2,2,1,1] .empty .empty) .empty)) (.node [11,11,11,10,3,3,3,3,3,1,1,1,1] (.node [11,11,11,10,3,3,3,3,2,2,2,1] (.node [11,11,11,10,3,3,3,3,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,3,3,3,3,3,2,1,1] .empty .empty))))

def degreeTree62_294 : RowTree := (.node [11,11,11,10,4,3,3,3,3,1,1,1] (.node [11,11,11,10,4,3,3,2,2,2,1,1,1] (.node [11,11,11,10,4,3,2,2,2,2,2,1,1] (.node [11,11,11,10,4,3,2,2,2,2,1,1,1,1] (.node [11,11,11,10,4,2,2,2,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,11,10,4,3,3,2,2,1,1,1,1,1] (.node [11,11,11,10,4,3,2,2,2,2,2,2] .empty .empty) .empty)) (.node [11,11,11,10,4,3,3,3,2,1,1,1,1] (.node [11,11,11,10,4,3,3,3,1,1,1,1,1,1] (.node [11,11,11,10,4,3,3,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,11,10,4,3,3,3,2,2,1,1] .empty .empty))) (.node [11,11,11,10,4,4,3,2,2,2,1,1] (.node [11,11,11,10,4,4,2,2,2,2,2,1] (.node [11,11,11,10,4,4,2,2,2,2,1,1,1] (.node [11,11,11,10,4,4,2,2,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,4,4,3,2,2,1,1,1,1] (.node [11,11,11,10,4,4,3,2,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,10,4,4,4,1,1,1,1,1,1,1] (.node [11,11,11,10,4,4,3,3,2,1,1,1] (.node [11,11,11,10,4,4,3,3,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,4,4,4,2,1,1,1,1,1] .empty .empty))))

def degreeTree62_295 : RowTree := (.node [11,11,11,10,4,2,2,2,2,2,2,1,1,1] degreeTree62_293 degreeTree62_294)

def degreeTree62_296 : RowTree := (.node [11,11,11,10,5,3,3,3,1,1,1,1,1] (.node [11,11,11,10,5,3,2,2,2,2,1,1,1] (.node [11,11,11,10,5,2,2,2,2,2,2,1,1] (.node [11,11,11,10,5,2,2,2,2,2,1,1,1,1] (.node [11,11,11,10,4,4,4,3,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,5,3,2,2,2,1,1,1,1,1] (.node [11,11,11,10,5,2,2,2,2,2,2,2] .empty .empty) .empty)) (.node [11,11,11,10,5,3,3,2,2,1,1,1,1] (.node [11,11,11,10,5,3,3,2,1,1,1,1,1,1] (.node [11,11,11,10,5,3,2,2,2,2,2,1] .empty .empty) .empty) (.node [11,11,11,10,5,3,3,2,2,2,1,1] .empty .empty))) (.node [11,11,11,10,5,4,3,2,1,1,1,1,1] (.node [11,11,11,10,5,4,2,2,2,1,1,1,1] (.node [11,11,11,10,5,4,2,2,1,1,1,1,1,1] (.node [11,11,11,10,5,3,3,3,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,5,4,3,1,1,1,1,1,1,1] (.node [11,11,11,10,5,4,2,2,2,2,1,1] .empty .empty) .empty)) (.node [11,11,11,10,5,4,4,1,1,1,1,1,1] (.node [11,11,11,10,5,4,3,3,1,1,1,1] (.node [11,11,11,10,5,4,3,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,5,4,4,2,1,1,1,1] .empty .empty))))

def degreeTree62_297 : RowTree := (.node [11,11,11,10,6,3,2,2,2,2,1,1] (.node [11,11,11,10,6,2,2,2,2,1,1,1,1,1] (.node [11,11,11,10,5,5,3,1,1,1,1,1,1] (.node [11,11,11,10,5,5,2,2,2,1,1,1] (.node [11,11,11,10,5,5,2,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,5,5,4,1,1,1,1,1] (.node [11,11,11,10,5,5,3,2,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,10,6,3,2,2,1,1,1,1,1,1] (.node [11,11,11,10,6,2,2,2,2,2,2,1] (.node [11,11,11,10,6,2,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,6,3,2,2,2,1,1,1,1] .empty .empty))) (.node [11,11,11,10,6,4,2,2,1,1,1,1,1] (.node [11,11,11,10,6,3,3,2,2,1,1,1] (.node [11,11,11,10,6,3,3,2,1,1,1,1,1] (.node [11,11,11,10,6,3,3,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,6,4,2,1,1,1,1,1,1,1] (.node [11,11,11,10,6,3,3,3,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,10,6,4,3,2,1,1,1,1] (.node [11,11,11,10,6,4,3,1,1,1,1,1,1] (.node [11,11,11,10,6,4,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,6,4,4,1,1,1,1,1] .empty .empty))))

def degreeTree62_298 : RowTree := (.node [11,11,11,10,5,5,2,1,1,1,1,1,1,1] degreeTree62_296 degreeTree62_297)

def degreeTree62_299 : RowTree := (.node [11,11,11,10,4,4,4,2,2,1,1,1] degreeTree62_295 degreeTree62_298)

def degreeTree62_300 : RowTree := (.node [11,11,11,9,9,2,2,2,1,1,1,1,1] degreeTree62_292 degreeTree62_299)

def degreeTree62_301 : RowTree := (.node [11,11,11,10,7,3,2,2,2,1,1,1] (.node [11,11,11,10,7,2,2,2,1,1,1,1,1,1] (.node [11,11,11,10,6,5,3,1,1,1,1,1] (.node [11,11,11,10,6,5,2,2,1,1,1,1] (.node [11,11,11,10,6,5,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,6,6,2,1,1,1,1,1] (.node [11,11,11,10,6,6,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,10,7,3,2,1,1,1,1,1,1,1] (.node [11,11,11,10,7,2,2,2,2,2,1,1] (.node [11,11,11,10,7,2,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,7,3,2,2,1,1,1,1,1] .empty .empty))) (.node [11,11,11,10,7,4,3,1,1,1,1,1] (.node [11,11,11,10,7,4,1,1,1,1,1,1,1,1] (.node [11,11,11,10,7,3,3,2,1,1,1,1] (.node [11,11,11,10,7,3,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,7,4,2,2,1,1,1,1] (.node [11,11,11,10,7,4,2,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,10,7,6,1,1,1,1,1,1] (.node [11,11,11,10,7,5,2,1,1,1,1,1] (.node [11,11,11,10,7,5,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,8,2,2,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_302 : RowTree := (.node [11,11,11,10,9,2,2,2,1,1,1,1] (.node [11,11,11,10,8,4,1,1,1,1,1,1,1] (.node [11,11,11,10,8,3,2,1,1,1,1,1,1] (.node [11,11,11,10,8,3,1,1,1,1,1,1,1,1] (.node [11,11,11,10,8,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,8,3,3,1,1,1,1,1] (.node [11,11,11,10,8,3,2,2,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,10,9,2,1,1,1,1,1,1,1,1] (.node [11,11,11,10,8,5,1,1,1,1,1,1] (.node [11,11,11,10,8,4,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,9,2,2,1,1,1,1,1,1] .empty .empty))) (.node [11,11,11,10,10,2,2,1,1,1,1,1] (.node [11,11,11,10,9,4,1,1,1,1,1,1] (.node [11,11,11,10,9,3,2,1,1,1,1,1] (.node [11,11,11,10,9,3,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,10,10,2,1,1,1,1,1,1,1] (.node [11,11,11,10,10,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,11,2,2,2,2,2,2,2,2,2] (.node [11,11,11,11,2,2,2,2,2,2,2,2,1,1] (.node [11,11,11,10,10,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,3,2,2,2,2,2,2,1,1,1] .empty .empty))))

def degreeTree62_303 : RowTree := (.node [11,11,11,10,8,2,2,2,1,1,1,1,1] degreeTree62_301 degreeTree62_302)

def degreeTree62_304 : RowTree := (.node [11,11,11,11,4,2,2,2,2,2,1,1,1,1] (.node [11,11,11,11,3,3,3,2,2,2,2,1] (.node [11,11,11,11,3,3,2,2,2,2,2,2] (.node [11,11,11,11,3,3,2,2,2,2,2,1,1] (.node [11,11,11,11,3,3,2,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,3,3,3,2,2,2,1,1,1] (.node [11,11,11,11,3,3,3,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,11,3,3,3,3,2,2,1,1] (.node [11,11,11,11,3,3,3,3,2,1,1,1,1] (.node [11,11,11,11,3,3,3,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,3,3,3,3,3,1,1,1] .empty .empty))) (.node [11,11,11,11,4,3,3,2,1,1,1,1,1,1] (.node [11,11,11,11,4,3,2,2,2,1,1,1,1,1] (.node [11,11,11,11,4,2,2,2,2,2,2,2] (.node [11,11,11,11,4,2,2,2,2,2,2,1,1] .empty .empty) .empty) (.node [11,11,11,11,4,3,2,2,2,2,2,1] (.node [11,11,11,11,4,3,2,2,2,2,1,1,1] .empty .empty) .empty)) (.node [11,11,11,11,4,3,3,3,1,1,1,1,1] (.node [11,11,11,11,4,3,3,2,2,2,1,1] (.node [11,11,11,11,4,3,3,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,4,3,3,3,2,1,1,1] .empty .empty))))

def degreeTree62_305 : RowTree := (.node [11,11,11,11,5,2,2,2,2,2,2,1] (.node [11,11,11,11,4,4,3,3,1,1,1,1] (.node [11,11,11,11,4,4,3,1,1,1,1,1,1,1] (.node [11,11,11,11,4,4,2,2,2,2,1,1] (.node [11,11,11,11,4,4,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,4,4,3,2,2,1,1,1] (.node [11,11,11,11,4,4,3,2,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,11,5,2,2,2,2,1,1,1,1,1] (.node [11,11,11,11,4,4,4,2,1,1,1,1] (.node [11,11,11,11,4,4,4,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,5,2,2,2,2,2,1,1,1] .empty .empty))) (.node [11,11,11,11,5,3,3,2,2,1,1,1] (.node [11,11,11,11,5,3,2,2,2,2,1,1] (.node [11,11,11,11,5,3,2,2,2,1,1,1,1] (.node [11,11,11,11,5,3,2,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,5,3,3,2,1,1,1,1,1] (.node [11,11,11,11,5,3,3,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,11,5,4,2,2,1,1,1,1,1] (.node [11,11,11,11,5,4,2,1,1,1,1,1,1,1] (.node [11,11,11,11,5,3,3,3,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,5,4,2,2,2,1,1,1] .empty .empty))))

def degreeTree62_306 : RowTree := (.node [11,11,11,11,4,4,2,2,1,1,1,1,1,1] degreeTree62_304 degreeTree62_305)

def degreeTree62_307 : RowTree := (.node [11,11,11,11,3,2,2,2,2,2,2,2,1] degreeTree62_303 degreeTree62_306)

def degreeTree62_308 : RowTree := (.node [11,11,11,11,6,3,2,2,1,1,1,1,1] (.node [11,11,11,11,5,5,3,1,1,1,1,1] (.node [11,11,11,11,5,5,1,1,1,1,1,1,1,1] (.node [11,11,11,11,5,4,4,1,1,1,1,1] (.node [11,11,11,11,5,4,3,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,5,5,2,2,1,1,1,1] (.node [11,11,11,11,5,5,2,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,11,6,2,2,2,2,2,1,1] (.node [11,11,11,11,6,2,2,2,2,1,1,1,1] (.node [11,11,11,11,6,2,2,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,6,3,2,1,1,1,1,1,1,1] .empty .empty))) (.node [11,11,11,11,6,4,2,2,1,1,1,1] (.node [11,11,11,11,6,3,3,2,1,1,1,1] (.node [11,11,11,11,6,3,3,1,1,1,1,1,1] (.node [11,11,11,11,6,3,2,2,2,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,6,4,2,1,1,1,1,1,1] (.node [11,11,11,11,6,4,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,11,6,5,2,1,1,1,1,1] (.node [11,11,11,11,6,5,1,1,1,1,1,1,1] (.node [11,11,11,11,6,4,3,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,6,6,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_309 : RowTree := (.node [11,11,11,11,8,2,2,1,1,1,1,1,1] (.node [11,11,11,11,7,3,3,1,1,1,1,1] (.node [11,11,11,11,7,3,1,1,1,1,1,1,1,1] (.node [11,11,11,11,7,2,2,2,2,1,1,1] (.node [11,11,11,11,7,2,2,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,7,3,2,2,1,1,1,1] (.node [11,11,11,11,7,3,2,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,11,7,5,1,1,1,1,1,1] (.node [11,11,11,11,7,4,2,1,1,1,1,1] (.node [11,11,11,11,7,4,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,8,2,1,1,1,1,1,1,1,1] .empty .empty))) (.node [11,11,11,11,9,2,1,1,1,1,1,1,1] (.node [11,11,11,11,8,3,2,1,1,1,1,1] (.node [11,11,11,11,8,3,1,1,1,1,1,1,1] (.node [11,11,11,11,8,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,9,1,1,1,1,1,1,1,1,1] (.node [11,11,11,11,8,4,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,11,11,11,10,1,1,1,1,1,1,1,1] (.node [11,11,11,11,9,3,1,1,1,1,1,1] (.node [11,11,11,11,9,2,2,1,1,1,1,1] .empty .empty) .empty) (.node [11,11,11,11,10,2,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_310 : RowTree := (.node [11,11,11,11,7,2,2,1,1,1,1,1,1,1] degreeTree62_308 degreeTree62_309)

def degreeTree62_311 : RowTree := (.node [12,6,6,6,6,6,6,6,2,2,2,1,1] (.node [12,6,6,6,6,6,6,5,3,2,2,1,1] (.node [12,6,6,6,6,6,5,5,5,2,1,1,1] (.node [12,6,6,6,6,6,5,5,4,2,2,1,1] (.node [12,6,6,6,6,5,5,5,5,2,2,1,1] .empty .empty) .empty) (.node [12,6,6,6,6,6,6,4,4,2,2,1,1] (.node [12,6,6,6,6,6,5,5,5,2,2,1] .empty .empty) .empty)) (.node [12,6,6,6,6,6,6,5,5,1,1,1,1] (.node [12,6,6,6,6,6,6,5,4,2,2,1] (.node [12,6,6,6,6,6,6,5,4,2,1,1,1] .empty .empty) .empty) (.node [12,6,6,6,6,6,6,5,5,2,1,1] .empty .empty))) (.node [12,7,6,6,5,5,5,5,5,2,2,1,1] (.node [12,6,6,6,6,6,6,6,4,1,1,1,1] (.node [12,6,6,6,6,6,6,6,3,2,2,1] (.node [12,6,6,6,6,6,6,6,3,2,1,1,1] .empty .empty) .empty) (.node [12,6,6,6,6,6,6,6,5,1,1,1] (.node [12,6,6,6,6,6,6,6,4,2,1,1] .empty .empty) .empty)) (.node [12,7,6,6,6,5,5,5,5,2,2,1] (.node [12,7,6,6,6,5,5,5,5,2,1,1,1] (.node [12,7,6,6,6,5,5,5,4,2,2,1,1] .empty .empty) .empty) (.node [12,7,6,6,6,6,5,4,4,2,2,1,1] .empty .empty))))

def degreeTree62_312 : RowTree := (.node [12,7,6,6,6,6,6,5,4,1,1,1,1] (.node [12,7,6,6,6,6,6,4,4,2,1,1,1] (.node [12,7,6,6,6,6,5,5,5,1,1,1,1] (.node [12,7,6,6,6,6,5,5,4,2,2,1] (.node [12,7,6,6,6,6,5,5,4,2,1,1,1] .empty .empty) .empty) (.node [12,7,6,6,6,6,6,4,3,2,2,1,1] (.node [12,7,6,6,6,6,5,5,5,2,1,1] .empty .empty) .empty)) (.node [12,7,6,6,6,6,6,5,3,2,1,1,1] (.node [12,7,6,6,6,6,6,5,2,2,2,1,1] (.node [12,7,6,6,6,6,6,4,4,2,2,1] .empty .empty) .empty) (.node [12,7,6,6,6,6,6,5,3,2,2,1] .empty .empty))) (.node [12,7,6,6,6,6,6,6,3,1,1,1,1] (.node [12,7,6,6,6,6,6,6,2,2,1,1,1] (.node [12,7,6,6,6,6,6,5,5,1,1,1] (.node [12,7,6,6,6,6,6,5,4,2,1,1] .empty .empty) .empty) (.node [12,7,6,6,6,6,6,6,2,2,2,1] .empty .empty)) (.node [12,7,7,5,5,5,5,5,5,2,2,1,1] (.node [12,7,6,6,6,6,6,6,4,1,1,1] (.node [12,7,6,6,6,6,6,6,3,2,1,1] .empty .empty) .empty) (.node [12,7,7,6,5,5,5,5,4,2,2,1,1] .empty .empty))))

def degreeTree62_313 : RowTree := (.node [12,7,6,6,6,6,5,5,3,2,2,1,1] degreeTree62_311 degreeTree62_312)

def degreeTree62_314 : RowTree := (.node [11,11,11,11,11,1,1,1,1,1,1,1] degreeTree62_310 degreeTree62_313)

def degreeTree62_315 : RowTree := (.node [11,11,11,11,5,4,3,1,1,1,1,1,1] degreeTree62_307 degreeTree62_314)

def degreeTree62_316 : RowTree := (.node [11,11,11,10,6,5,1,1,1,1,1,1,1,1] degreeTree62_300 degreeTree62_315)

def degreeTree62_317 : RowTree := (.node [11,11,11,9,5,4,3,2,1,1,1,1,1,1] degreeTree62_285 degreeTree62_316)

def degreeTree62_318 : RowTree := (.node [12,7,7,6,6,6,5,4,4,2,2,1] (.node [12,7,7,6,6,5,5,5,5,1,1,1,1] (.node [12,7,7,6,6,5,5,5,3,2,2,1,1] (.node [12,7,7,6,6,5,5,4,4,2,2,1,1] (.node [12,7,7,6,5,5,5,5,5,2,2,1] .empty .empty) .empty) (.node [12,7,7,6,6,5,5,5,4,2,2,1] (.node [12,7,7,6,6,5,5,5,4,2,1,1,1] .empty .empty) .empty)) (.node [12,7,7,6,6,6,5,4,3,2,2,1,1] (.node [12,7,7,6,6,6,4,4,4,2,2,1,1] (.node [12,7,7,6,6,5,5,5,5,2,1,1] .empty .empty) .empty) (.node [12,7,7,6,6,6,5,4,4,2,1,1,1] .empty .empty))) (.node [12,7,7,6,6,6,5,5,5,1,1,1] (.node [12,7,7,6,6,6,5,5,3,2,2,1] (.node [12,7,7,6,6,6,5,5,3,2,1,1,1] (.node [12,7,7,6,6,6,5,5,2,2,2,1,1] .empty .empty) .empty) (.node [12,7,7,6,6,6,5,5,4,2,1,1] (.node [12,7,7,6,6,6,5,5,4,1,1,1,1] .empty .empty) .empty)) (.node [12,7,7,6,6,6,6,4,2,2,2,1,1] (.node [12,7,7,6,6,6,6,3,3,2,2,1,1] (.node [12,7,7,6,6,6,6,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,7,7,6,6,6,6,4,3,2,1,1,1] .empty .empty))))

def degreeTree62_319 : RowTree := (.node [12,7,7,7,5,5,5,4,4,2,2,1,1] (.node [12,7,7,6,6,6,6,5,3,2,1,1] (.node [12,7,7,6,6,6,6,5,2,2,1,1,1] (.node [12,7,7,6,6,6,6,4,4,2,1,1] (.node [12,7,7,6,6,6,6,4,4,1,1,1,1] .empty .empty) .empty) (.node [12,7,7,6,6,6,6,5,3,1,1,1,1] (.node [12,7,7,6,6,6,6,5,2,2,2,1] .empty .empty) .empty)) (.node [12,7,7,6,6,6,6,6,2,2,1,1] (.node [12,7,7,6,6,6,6,6,2,1,1,1,1] (.node [12,7,7,6,6,6,6,5,4,1,1,1] .empty .empty) .empty) (.node [12,7,7,6,6,6,6,6,3,1,1,1] .empty .empty))) (.node [12,7,7,7,6,5,4,4,4,2,2,1,1] (.node [12,7,7,7,5,5,5,5,4,2,2,1] (.node [12,7,7,7,5,5,5,5,4,2,1,1,1] (.node [12,7,7,7,5,5,5,5,3,2,2,1,1] .empty .empty) .empty) (.node [12,7,7,7,5,5,5,5,5,2,1,1] (.node [12,7,7,7,5,5,5,5,5,1,1,1,1] .empty .empty) .empty)) (.node [12,7,7,7,6,5,5,4,4,2,2,1] (.node [12,7,7,7,6,5,5,4,4,2,1,1,1] (.node [12,7,7,7,6,5,5,4,3,2,2,1,1] .empty .empty) .empty) (.node [12,7,7,7,6,5,5,5,2,2,2,1,1] .empty .empty))))

def degreeTree62_320 : RowTree := (.node [12,7,7,6,6,6,6,4,3,2,2,1] degreeTree62_318 degreeTree62_319)

def degreeTree62_321 : RowTree := (.node [12,7,7,7,6,6,5,4,3,2,1,1,1] (.node [12,7,7,7,6,6,4,4,4,2,1,1,1] (.node [12,7,7,7,6,5,5,5,4,2,1,1] (.node [12,7,7,7,6,5,5,5,4,1,1,1,1] (.node [12,7,7,7,6,5,5,5,3,2,2,1] .empty .empty) .empty) (.node [12,7,7,7,6,6,4,4,3,2,2,1,1] (.node [12,7,7,7,6,5,5,5,5,1,1,1] .empty .empty) .empty)) (.node [12,7,7,7,6,6,5,3,3,2,2,1,1] (.node [12,7,7,7,6,6,5,2,2,2,2,2,2] (.node [12,7,7,7,6,6,4,4,4,2,2,1] .empty .empty) .empty) (.node [12,7,7,7,6,6,5,4,2,2,2,1,1] .empty .empty))) (.node [12,7,7,7,6,6,5,5,3,1,1,1,1] (.node [12,7,7,7,6,6,5,4,4,2,1,1] (.node [12,7,7,7,6,6,5,4,4,1,1,1,1] (.node [12,7,7,7,6,6,5,4,3,2,2,1] .empty .empty) .empty) (.node [12,7,7,7,6,6,5,5,2,2,2,1] (.node [12,7,7,7,6,6,5,5,2,2,1,1,1] .empty .empty) .empty)) (.node [12,7,7,7,6,6,6,2,2,2,2,2,1] (.node [12,7,7,7,6,6,5,5,4,1,1,1] (.node [12,7,7,7,6,6,5,5,3,2,1,1] .empty .empty) .empty) (.node [12,7,7,7,6,6,6,3,2,2,2,1,1] .empty .empty))))

def degreeTree62_322 : RowTree := (.node [12,7,7,7,6,6,6,6,2,1,1,1] (.node [12,7,7,7,6,6,6,4,4,1,1,1] (.node [12,7,7,7,6,6,6,4,2,2,2,1] (.node [12,7,7,7,6,6,6,4,2,2,1,1,1] (.node [12,7,7,7,6,6,6,3,3,2,2,1] .empty .empty) .empty) (.node [12,7,7,7,6,6,6,4,3,2,1,1] (.node [12,7,7,7,6,6,6,4,3,1,1,1,1] .empty .empty) .empty)) (.node [12,7,7,7,6,6,6,5,3,1,1,1] (.node [12,7,7,7,6,6,6,5,2,2,1,1] (.node [12,7,7,7,6,6,6,5,2,1,1,1,1] .empty .empty) .empty) (.node [12,7,7,7,6,6,6,6,1,1,1,1,1] .empty .empty))) (.node [12,7,7,7,7,5,5,3,3,2,2,1,1] (.node [12,7,7,7,7,5,4,4,4,2,1,1,1] (.node [12,7,7,7,7,5,4,4,3,2,2,1,1] (.node [12,7,7,7,7,4,4,4,4,2,2,1,1] .empty .empty) .empty) (.node [12,7,7,7,7,5,5,2,2,2,2,2,2] (.node [12,7,7,7,7,5,4,4,4,2,2,1] .empty .empty) .empty)) (.node [12,7,7,7,7,5,5,4,3,2,2,1] (.node [12,7,7,7,7,5,5,4,3,2,1,1,1] (.node [12,7,7,7,7,5,5,4,2,2,2,1,1] .empty .empty) .empty) (.node [12,7,7,7,7,5,5,4,4,1,1,1,1] .empty .empty))))

def degreeTree62_323 : RowTree := (.node [12,7,7,7,6,6,6,3,3,2,1,1,1] degreeTree62_321 degreeTree62_322)

def degreeTree62_324 : RowTree := (.node [12,7,7,7,6,5,5,5,3,2,1,1,1] degreeTree62_320 degreeTree62_323)

def degreeTree62_325 : RowTree := (.node [12,7,7,7,7,6,4,4,4,1,1,1,1] (.node [12,7,7,7,7,6,4,2,2,2,2,2,2] (.node [12,7,7,7,7,5,5,5,3,1,1,1,1] (.node [12,7,7,7,7,5,5,5,2,2,2,1] (.node [12,7,7,7,7,5,5,5,2,2,1,1,1] .empty .empty) .empty) (.node [12,7,7,7,7,5,5,5,4,1,1,1] (.node [12,7,7,7,7,5,5,5,3,2,1,1] .empty .empty) .empty)) (.node [12,7,7,7,7,6,4,4,3,2,1,1,1] (.node [12,7,7,7,7,6,4,4,2,2,2,1,1] (.node [12,7,7,7,7,6,4,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,7,7,7,7,6,4,4,3,2,2,1] .empty .empty))) (.node [12,7,7,7,7,6,5,4,2,2,1,1,1] (.node [12,7,7,7,7,6,5,3,2,2,2,1,1] (.node [12,7,7,7,7,6,5,2,2,2,2,2,1] (.node [12,7,7,7,7,6,4,4,4,2,1,1] .empty .empty) .empty) (.node [12,7,7,7,7,6,5,3,3,2,2,1] (.node [12,7,7,7,7,6,5,3,3,2,1,1,1] .empty .empty) .empty)) (.node [12,7,7,7,7,6,5,4,3,2,1,1] (.node [12,7,7,7,7,6,5,4,3,1,1,1,1] (.node [12,7,7,7,7,6,5,4,2,2,2,1] .empty .empty) .empty) (.node [12,7,7,7,7,6,5,4,4,1,1,1] .empty .empty))))

def degreeTree62_326 : RowTree := (.node [12,7,7,7,7,6,6,4,3,1,1,1] (.node [12,7,7,7,7,6,6,3,2,2,2,1] (.node [12,7,7,7,7,6,6,2,2,2,2,1,1] (.node [12,7,7,7,7,6,5,5,3,1,1,1] (.node [12,7,7,7,7,6,5,5,2,2,1,1] .empty .empty) .empty) (.node [12,7,7,7,7,6,6,3,2,2,1,1,1] (.node [12,7,7,7,7,6,6,2,2,2,2,2] .empty .empty) .empty)) (.node [12,7,7,7,7,6,6,4,2,1,1,1,1] (.node [12,7,7,7,7,6,6,3,3,2,1,1] (.node [12,7,7,7,7,6,6,3,3,1,1,1,1] .empty .empty) .empty) (.node [12,7,7,7,7,6,6,4,2,2,1,1] .empty .empty))) (.node [12,7,7,7,7,7,4,2,2,2,2,2,1] (.node [12,7,7,7,7,6,6,6,1,1,1,1] (.node [12,7,7,7,7,6,6,5,2,1,1,1] (.node [12,7,7,7,7,6,6,5,1,1,1,1,1] .empty .empty) .empty) (.node [12,7,7,7,7,7,3,3,3,2,2,1,1] (.node [12,7,7,7,7,7,3,2,2,2,2,2,2] .empty .empty) .empty)) (.node [12,7,7,7,7,7,4,3,3,2,2,1] (.node [12,7,7,7,7,7,4,3,3,2,1,1,1] (.node [12,7,7,7,7,7,4,3,2,2,2,1,1] .empty .empty) .empty) (.node [12,7,7,7,7,7,4,4,2,2,1,1,1] .empty .empty))))

def degreeTree62_327 : RowTree := (.node [12,7,7,7,7,6,5,5,2,1,1,1,1] degreeTree62_325 degreeTree62_326)

def degreeTree62_328 : RowTree := (.node [12,7,7,7,7,7,5,4,2,2,1,1] (.node [12,7,7,7,7,7,5,3,2,2,1,1,1] (.node [12,7,7,7,7,7,4,4,4,1,1,1] (.node [12,7,7,7,7,7,4,4,3,2,1,1] (.node [12,7,7,7,7,7,4,4,3,1,1,1,1] .empty .empty) .empty) (.node [12,7,7,7,7,7,5,2,2,2,2,2] (.node [12,7,7,7,7,7,5,2,2,2,2,1,1] .empty .empty) .empty)) (.node [12,7,7,7,7,7,5,3,3,2,1,1] (.node [12,7,7,7,7,7,5,3,3,1,1,1,1] (.node [12,7,7,7,7,7,5,3,2,2,2,1] .empty .empty) .empty) (.node [12,7,7,7,7,7,5,4,2,1,1,1,1] .empty .empty))) (.node [12,7,7,7,7,7,6,3,2,1,1,1,1] (.node [12,7,7,7,7,7,5,5,2,1,1,1] (.node [12,7,7,7,7,7,5,5,1,1,1,1,1] (.node [12,7,7,7,7,7,5,4,3,1,1,1] .empty .empty) .empty) (.node [12,7,7,7,7,7,6,2,2,2,2,1] (.node [12,7,7,7,7,7,6,2,2,2,1,1,1] .empty .empty) .empty)) (.node [12,7,7,7,7,7,6,4,1,1,1,1,1] (.node [12,7,7,7,7,7,6,3,3,1,1,1] (.node [12,7,7,7,7,7,6,3,2,2,1,1] .empty .empty) .empty) (.node [12,7,7,7,7,7,6,4,2,1,1,1] .empty .empty))))

def degreeTree62_329 : RowTree := (.node [12,8,6,6,6,5,5,4,4,2,2,1,1] (.node [12,7,7,7,7,7,7,4,1,1,1,1] (.node [12,7,7,7,7,7,7,2,2,2,1,1] (.node [12,7,7,7,7,7,7,2,2,1,1,1,1] (.node [12,7,7,7,7,7,7,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,7,7,7,7,7,7,3,2,1,1,1] (.node [12,7,7,7,7,7,7,3,1,1,1,1,1] .empty .empty) .empty)) (.node [12,8,6,6,5,5,5,5,5,2,1,1,1] (.node [12,8,6,6,5,5,5,5,4,2,2,1,1] (.node [12,8,6,5,5,5,5,5,5,2,2,1,1] .empty .empty) .empty) (.node [12,8,6,6,5,5,5,5,5,2,2,1] .empty .empty))) (.node [12,8,6,6,6,6,4,4,4,2,2,1,1] (.node [12,8,6,6,6,5,5,5,4,2,2,1] (.node [12,8,6,6,6,5,5,5,4,2,1,1,1] (.node [12,8,6,6,6,5,5,5,3,2,2,1,1] .empty .empty) .empty) (.node [12,8,6,6,6,5,5,5,5,2,1,1] (.node [12,8,6,6,6,5,5,5,5,1,1,1,1] .empty .empty) .empty)) (.node [12,8,6,6,6,6,5,4,4,2,2,1] (.node [12,8,6,6,6,6,5,4,4,2,1,1,1] (.node [12,8,6,6,6,6,5,4,3,2,2,1,1] .empty .empty) .empty) (.node [12,8,6,6,6,6,5,5,2,2,2,1,1] .empty .empty))))

def degreeTree62_330 : RowTree := (.node [12,7,7,7,7,7,6,5,1,1,1,1] degreeTree62_328 degreeTree62_329)

def degreeTree62_331 : RowTree := (.node [12,7,7,7,7,7,4,4,2,2,2,1] degreeTree62_327 degreeTree62_330)

def degreeTree62_332 : RowTree := (.node [12,7,7,7,7,5,5,4,4,2,1,1] degreeTree62_324 degreeTree62_331)

def degreeTree62_333 : RowTree := (.node [12,8,6,6,6,6,6,4,4,2,1,1] (.node [12,8,6,6,6,6,6,3,3,2,2,1,1] (.node [12,8,6,6,6,6,5,5,4,2,1,1] (.node [12,8,6,6,6,6,5,5,4,1,1,1,1] (.node [12,8,6,6,6,6,5,5,3,2,2,1] .empty .empty) .empty) (.node [12,8,6,6,6,6,6,2,2,2,2,2,2] (.node [12,8,6,6,6,6,5,5,5,1,1,1] .empty .empty) .empty)) (.node [12,8,6,6,6,6,6,4,3,2,2,1] (.node [12,8,6,6,6,6,6,4,3,2,1,1,1] (.node [12,8,6,6,6,6,6,4,2,2,2,1,1] .empty .empty) .empty) (.node [12,8,6,6,6,6,6,4,4,1,1,1,1] .empty .empty))) (.node [12,8,6,6,6,6,6,6,2,1,1,1,1] (.node [12,8,6,6,6,6,6,5,3,1,1,1,1] (.node [12,8,6,6,6,6,6,5,2,2,2,1] (.node [12,8,6,6,6,6,6,5,2,2,1,1,1] .empty .empty) .empty) (.node [12,8,6,6,6,6,6,5,4,1,1,1] (.node [12,8,6,6,6,6,6,5,3,2,1,1] .empty .empty) .empty)) (.node [12,8,7,5,5,5,5,5,4,2,2,1,1] (.node [12,8,6,6,6,6,6,6,3,1,1,1] (.node [12,8,6,6,6,6,6,6,2,2,1,1] .empty .empty) .empty) (.node [12,8,7,5,5,5,5,5,5,2,1,1,1] .empty .empty))))

def degreeTree62_334 : RowTree := (.node [12,8,7,6,6,5,5,5,2,2,2,1,1] (.node [12,8,7,6,5,5,5,5,5,2,1,1] (.node [12,8,7,6,5,5,5,5,4,2,1,1,1] (.node [12,8,7,6,5,5,5,5,3,2,2,1,1] (.node [12,8,7,6,5,5,5,4,4,2,2,1,1] .empty .empty) .empty) (.node [12,8,7,6,5,5,5,5,5,1,1,1,1] (.node [12,8,7,6,5,5,5,5,4,2,2,1] .empty .empty) .empty)) (.node [12,8,7,6,6,5,5,4,4,2,1,1,1] (.node [12,8,7,6,6,5,5,4,3,2,2,1,1] (.node [12,8,7,6,6,5,4,4,4,2,2,1,1] .empty .empty) .empty) (.node [12,8,7,6,6,5,5,4,4,2,2,1] .empty .empty))) (.node [12,8,7,6,6,6,4,4,3,2,2,1,1] (.node [12,8,7,6,6,5,5,5,4,1,1,1,1] (.node [12,8,7,6,6,5,5,5,3,2,2,1] (.node [12,8,7,6,6,5,5,5,3,2,1,1,1] .empty .empty) .empty) (.node [12,8,7,6,6,5,5,5,5,1,1,1] (.node [12,8,7,6,6,5,5,5,4,2,1,1] .empty .empty) .empty)) (.node [12,8,7,6,6,6,5,2,2,2,2,2,2] (.node [12,8,7,6,6,6,4,4,4,2,2,1] (.node [12,8,7,6,6,6,4,4,4,2,1,1,1] .empty .empty) .empty) (.node [12,8,7,6,6,6,5,3,3,2,2,1,1] .empty .empty))))

def degreeTree62_335 : RowTree := (.node [12,8,7,5,5,5,5,5,5,2,2,1] degreeTree62_333 degreeTree62_334)

def degreeTree62_336 : RowTree := (.node [12,8,7,6,6,6,6,3,2,2,2,1,1] (.node [12,8,7,6,6,6,5,5,2,2,2,1] (.node [12,8,7,6,6,6,5,4,4,1,1,1,1] (.node [12,8,7,6,6,6,5,4,3,2,2,1] (.node [12,8,7,6,6,6,5,4,3,2,1,1,1] .empty .empty) .empty) (.node [12,8,7,6,6,6,5,5,2,2,1,1,1] (.node [12,8,7,6,6,6,5,4,4,2,1,1] .empty .empty) .empty)) (.node [12,8,7,6,6,6,5,5,4,1,1,1] (.node [12,8,7,6,6,6,5,5,3,2,1,1] (.node [12,8,7,6,6,6,5,5,3,1,1,1,1] .empty .empty) .empty) (.node [12,8,7,6,6,6,6,2,2,2,2,2,1] .empty .empty))) (.node [12,8,7,6,6,6,6,4,3,2,1,1] (.node [12,8,7,6,6,6,6,4,2,2,1,1,1] (.node [12,8,7,6,6,6,6,3,3,2,2,1] (.node [12,8,7,6,6,6,6,3,3,2,1,1,1] .empty .empty) .empty) (.node [12,8,7,6,6,6,6,4,3,1,1,1,1] (.node [12,8,7,6,6,6,6,4,2,2,2,1] .empty .empty) .empty)) (.node [12,8,7,6,6,6,6,5,2,2,1,1] (.node [12,8,7,6,6,6,6,5,2,1,1,1,1] (.node [12,8,7,6,6,6,6,4,4,1,1,1] .empty .empty) .empty) (.node [12,8,7,6,6,6,6,5,3,1,1,1] .empty .empty))))

def degreeTree62_337 : RowTree := (.node [12,8,7,7,5,5,5,5,5,1,1,1] (.node [12,8,7,7,5,5,5,5,2,2,2,1,1] (.node [12,8,7,7,5,5,5,4,3,2,2,1,1] (.node [12,8,7,7,5,5,4,4,4,2,2,1,1] (.node [12,8,7,6,6,6,6,6,2,1,1,1] .empty .empty) .empty) (.node [12,8,7,7,5,5,5,4,4,2,2,1] (.node [12,8,7,7,5,5,5,4,4,2,1,1,1] .empty .empty) .empty)) (.node [12,8,7,7,5,5,5,5,4,1,1,1,1] (.node [12,8,7,7,5,5,5,5,3,2,2,1] (.node [12,8,7,7,5,5,5,5,3,2,1,1,1] .empty .empty) .empty) (.node [12,8,7,7,5,5,5,5,4,2,1,1] .empty .empty))) (.node [12,8,7,7,6,5,5,3,3,2,2,1,1] (.node [12,8,7,7,6,5,4,4,4,2,1,1,1] (.node [12,8,7,7,6,5,4,4,3,2,2,1,1] (.node [12,8,7,7,6,4,4,4,4,2,2,1,1] .empty .empty) .empty) (.node [12,8,7,7,6,5,5,2,2,2,2,2,2] (.node [12,8,7,7,6,5,4,4,4,2,2,1] .empty .empty) .empty)) (.node [12,8,7,7,6,5,5,4,3,2,2,1] (.node [12,8,7,7,6,5,5,4,3,2,1,1,1] (.node [12,8,7,7,6,5,5,4,2,2,2,1,1] .empty .empty) .empty) (.node [12,8,7,7,6,5,5,4,4,1,1,1,1] .empty .empty))))

def degreeTree62_338 : RowTree := (.node [12,8,7,6,6,6,6,6,1,1,1,1,1] degreeTree62_336 degreeTree62_337)

def degreeTree62_339 : RowTree := (.node [12,8,7,6,6,6,5,4,2,2,2,1,1] degreeTree62_335 degreeTree62_338)

def degreeTree62_340 : RowTree := (.node [12,8,7,7,6,6,4,4,4,1,1,1,1] (.node [12,8,7,7,6,6,4,2,2,2,2,2,2] (.node [12,8,7,7,6,5,5,5,3,1,1,1,1] (.node [12,8,7,7,6,5,5,5,2,2,2,1] (.node [12,8,7,7,6,5,5,5,2,2,1,1,1] .empty .empty) .empty) (.node [12,8,7,7,6,5,5,5,4,1,1,1] (.node [12,8,7,7,6,5,5,5,3,2,1,1] .empty .empty) .empty)) (.node [12,8,7,7,6,6,4,4,3,2,1,1,1] (.node [12,8,7,7,6,6,4,4,2,2,2,1,1] (.node [12,8,7,7,6,6,4,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,8,7,7,6,6,4,4,3,2,2,1] .empty .empty))) (.node [12,8,7,7,6,6,5,4,2,2,1,1,1] (.node [12,8,7,7,6,6,5,3,2,2,2,1,1] (.node [12,8,7,7,6,6,5,2,2,2,2,2,1] (.node [12,8,7,7,6,6,4,4,4,2,1,1] .empty .empty) .empty) (.node [12,8,7,7,6,6,5,3,3,2,2,1] (.node [12,8,7,7,6,6,5,3,3,2,1,1,1] .empty .empty) .empty)) (.node [12,8,7,7,6,6,5,4,3,2,1,1] (.node [12,8,7,7,6,6,5,4,3,1,1,1,1] (.node [12,8,7,7,6,6,5,4,2,2,2,1] .empty .empty) .empty) (.node [12,8,7,7,6,6,5,4,4,1,1,1] .empty .empty))))

def degreeTree62_341 : RowTree := (.node [12,8,7,7,6,6,6,4,3,1,1,1] (.node [12,8,7,7,6,6,6,3,2,2,2,1] (.node [12,8,7,7,6,6,6,2,2,2,2,1,1] (.node [12,8,7,7,6,6,5,5,3,1,1,1] (.node [12,8,7,7,6,6,5,5,2,2,1,1] .empty .empty) .empty) (.node [12,8,7,7,6,6,6,3,2,2,1,1,1] (.node [12,8,7,7,6,6,6,2,2,2,2,2] .empty .empty) .empty)) (.node [12,8,7,7,6,6,6,4,2,1,1,1,1] (.node [12,8,7,7,6,6,6,3,3,2,1,1] (.node [12,8,7,7,6,6,6,3,3,1,1,1,1] .empty .empty) .empty) (.node [12,8,7,7,6,6,6,4,2,2,1,1] .empty .empty))) (.node [12,8,7,7,7,4,4,4,4,2,2,1] (.node [12,8,7,7,6,6,6,6,1,1,1,1] (.node [12,8,7,7,6,6,6,5,2,1,1,1] (.node [12,8,7,7,6,6,6,5,1,1,1,1,1] .empty .empty) .empty) (.node [12,8,7,7,7,4,4,4,4,2,1,1,1] (.node [12,8,7,7,7,4,4,4,3,2,2,1,1] .empty .empty) .empty)) (.node [12,8,7,7,7,5,4,4,2,2,2,1,1] (.node [12,8,7,7,7,5,4,3,3,2,2,1,1] (.node [12,8,7,7,7,5,4,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,8,7,7,7,5,4,4,3,2,1,1,1] .empty .empty))))

def degreeTree62_342 : RowTree := (.node [12,8,7,7,6,6,5,5,2,1,1,1,1] degreeTree62_340 degreeTree62_341)

def degreeTree62_343 : RowTree := (.node [12,8,7,7,7,5,5,4,4,1,1,1] (.node [12,8,7,7,7,5,5,3,3,2,2,1] (.node [12,8,7,7,7,5,5,2,2,2,2,2,1] (.node [12,8,7,7,7,5,4,4,4,2,1,1] (.node [12,8,7,7,7,5,4,4,4,1,1,1,1] .empty .empty) .empty) (.node [12,8,7,7,7,5,5,3,3,2,1,1,1] (.node [12,8,7,7,7,5,5,3,2,2,2,1,1] .empty .empty) .empty)) (.node [12,8,7,7,7,5,5,4,3,1,1,1,1] (.node [12,8,7,7,7,5,5,4,2,2,2,1] (.node [12,8,7,7,7,5,5,4,2,2,1,1,1] .empty .empty) .empty) (.node [12,8,7,7,7,5,5,4,3,2,1,1] .empty .empty))) (.node [12,8,7,7,7,6,4,2,2,2,2,2,1] (.node [12,8,7,7,7,5,5,5,3,1,1,1] (.node [12,8,7,7,7,5,5,5,2,2,1,1] (.node [12,8,7,7,7,5,5,5,2,1,1,1,1] .empty .empty) .empty) (.node [12,8,7,7,7,6,3,3,3,2,2,1,1] (.node [12,8,7,7,7,6,3,2,2,2,2,2,2] .empty .empty) .empty)) (.node [12,8,7,7,7,6,4,3,3,2,2,1] (.node [12,8,7,7,7,6,4,3,3,2,1,1,1] (.node [12,8,7,7,7,6,4,3,2,2,2,1,1] .empty .empty) .empty) (.node [12,8,7,7,7,6,4,4,2,2,1,1,1] .empty .empty))))

def degreeTree62_344 : RowTree := (.node [12,8,7,7,7,6,5,4,2,2,1,1] (.node [12,8,7,7,7,6,5,3,2,2,1,1,1] (.node [12,8,7,7,7,6,4,4,4,1,1,1] (.node [12,8,7,7,7,6,4,4,3,2,1,1] (.node [12,8,7,7,7,6,4,4,3,1,1,1,1] .empty .empty) .empty) (.node [12,8,7,7,7,6,5,2,2,2,2,2] (.node [12,8,7,7,7,6,5,2,2,2,2,1,1] .empty .empty) .empty)) (.node [12,8,7,7,7,6,5,3,3,2,1,1] (.node [12,8,7,7,7,6,5,3,3,1,1,1,1] (.node [12,8,7,7,7,6,5,3,2,2,2,1] .empty .empty) .empty) (.node [12,8,7,7,7,6,5,4,2,1,1,1,1] .empty .empty))) (.node [12,8,7,7,7,6,6,2,2,2,2,1] (.node [12,8,7,7,7,6,5,5,2,1,1,1] (.node [12,8,7,7,7,6,5,5,1,1,1,1,1] (.node [12,8,7,7,7,6,5,4,3,1,1,1] .empty .empty) .empty) (.node [12,8,7,7,7,6,6,2,2,2,1,1,1] .empty .empty)) (.node [12,8,7,7,7,6,6,3,3,1,1,1] (.node [12,8,7,7,7,6,6,3,2,2,1,1] (.node [12,8,7,7,7,6,6,3,2,1,1,1,1] .empty .empty) .empty) (.node [12,8,7,7,7,6,6,4,1,1,1,1,1] .empty .empty))))

def degreeTree62_345 : RowTree := (.node [12,8,7,7,7,6,4,4,2,2,2,1] degreeTree62_343 degreeTree62_344)

def degreeTree62_346 : RowTree := (.node [12,8,7,7,7,5,4,4,3,2,2,1] degreeTree62_342 degreeTree62_345)

def degreeTree62_347 : RowTree := (.node [12,8,7,7,6,5,5,4,4,2,1,1] degreeTree62_339 degreeTree62_346)

def degreeTree62_348 : RowTree := (.node [12,8,6,6,6,6,5,5,3,2,1,1,1] degreeTree62_332 degreeTree62_347)

def degreeTree62_349 : RowTree := (.node [12,8,7,7,7,7,4,3,3,1,1,1,1] (.node [12,8,7,7,7,7,3,3,3,2,2,1] (.node [12,8,7,7,7,7,3,2,2,2,2,2,1] (.node [12,8,7,7,7,7,2,2,2,2,2,2,2] (.node [12,8,7,7,7,6,6,5,1,1,1,1] .empty .empty) .empty) (.node [12,8,7,7,7,7,3,3,3,2,1,1,1] (.node [12,8,7,7,7,7,3,3,2,2,2,1,1] .empty .empty) .empty)) (.node [12,8,7,7,7,7,4,3,2,2,1,1,1] (.node [12,8,7,7,7,7,4,2,2,2,2,2] (.node [12,8,7,7,7,7,4,2,2,2,2,1,1] .empty .empty) .empty) (.node [12,8,7,7,7,7,4,3,2,2,2,1] .empty .empty))) (.node [12,8,7,7,7,7,5,2,2,2,2,1] (.node [12,8,7,7,7,7,4,4,2,2,1,1] (.node [12,8,7,7,7,7,4,4,2,1,1,1,1] (.node [12,8,7,7,7,7,4,3,3,2,1,1] .empty .empty) .empty) (.node [12,8,7,7,7,7,5,2,2,2,1,1,1] (.node [12,8,7,7,7,7,4,4,3,1,1,1] .empty .empty) .empty)) (.node [12,8,7,7,7,7,5,3,3,1,1,1] (.node [12,8,7,7,7,7,5,3,2,2,1,1] (.node [12,8,7,7,7,7,5,3,2,1,1,1,1] .empty .empty) .empty) (.node [12,8,7,7,7,7,5,4,1,1,1,1,1] .empty .empty))))

def degreeTree62_350 : RowTree := (.node [12,8,7,7,7,7,7,3,1,1,1,1] (.node [12,8,7,7,7,7,6,3,2,1,1,1] (.node [12,8,7,7,7,7,6,2,2,1,1,1,1] (.node [12,8,7,7,7,7,6,2,1,1,1,1,1,1] (.node [12,8,7,7,7,7,5,5,1,1,1,1] .empty .empty) .empty) (.node [12,8,7,7,7,7,6,3,1,1,1,1,1] (.node [12,8,7,7,7,7,6,2,2,2,1,1] .empty .empty) .empty)) (.node [12,8,7,7,7,7,7,2,1,1,1,1,1] (.node [12,8,7,7,7,7,7,1,1,1,1,1,1,1] (.node [12,8,7,7,7,7,6,4,1,1,1,1] .empty .empty) .empty) (.node [12,8,7,7,7,7,7,2,2,1,1,1] .empty .empty))) (.node [12,8,8,5,5,5,5,5,5,2,1,1] (.node [12,8,8,5,5,5,5,5,4,2,1,1,1] (.node [12,8,8,5,5,5,5,5,3,2,2,1,1] (.node [12,8,8,5,5,5,5,4,4,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,5,5,5,5,5,5,1,1,1,1] (.node [12,8,8,5,5,5,5,5,4,2,2,1] .empty .empty) .empty)) (.node [12,8,8,6,5,5,5,4,4,2,1,1,1] (.node [12,8,8,6,5,5,5,4,3,2,2,1,1] (.node [12,8,8,6,5,5,4,4,4,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,6,5,5,5,4,4,2,2,1] .empty .empty))))

def degreeTree62_351 : RowTree := (.node [12,8,7,7,7,7,5,4,2,1,1,1] degreeTree62_349 degreeTree62_350)

def degreeTree62_352 : RowTree := (.node [12,8,8,6,6,5,5,3,3,2,2,1,1] (.node [12,8,8,6,6,4,4,4,4,2,2,1,1] (.node [12,8,8,6,5,5,5,5,4,1,1,1,1] (.node [12,8,8,6,5,5,5,5,3,2,2,1] (.node [12,8,8,6,5,5,5,5,3,2,1,1,1] .empty .empty) .empty) (.node [12,8,8,6,5,5,5,5,5,1,1,1] (.node [12,8,8,6,5,5,5,5,4,2,1,1] .empty .empty) .empty)) (.node [12,8,8,6,6,5,4,4,4,2,2,1] (.node [12,8,8,6,6,5,4,4,4,2,1,1,1] (.node [12,8,8,6,6,5,4,4,3,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,6,6,5,5,2,2,2,2,2,2] .empty .empty))) (.node [12,8,8,6,6,5,5,5,2,2,1,1,1] (.node [12,8,8,6,6,5,5,4,3,2,2,1] (.node [12,8,8,6,6,5,5,4,3,2,1,1,1] (.node [12,8,8,6,6,5,5,4,2,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,6,6,5,5,4,4,2,1,1] (.node [12,8,8,6,6,5,5,4,4,1,1,1,1] .empty .empty) .empty)) (.node [12,8,8,6,6,5,5,5,3,2,1,1] (.node [12,8,8,6,6,5,5,5,3,1,1,1,1] (.node [12,8,8,6,6,5,5,5,2,2,2,1] .empty .empty) .empty) (.node [12,8,8,6,6,5,5,5,4,1,1,1] .empty .empty))))

def degreeTree62_353 : RowTree := (.node [12,8,8,6,6,6,5,4,2,2,1,1,1] (.node [12,8,8,6,6,6,4,4,4,2,1,1] (.node [12,8,8,6,6,6,4,4,3,2,1,1,1] (.node [12,8,8,6,6,6,4,4,2,2,2,1,1] (.node [12,8,8,6,6,6,4,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,6,6,6,4,4,4,1,1,1,1] (.node [12,8,8,6,6,6,4,4,3,2,2,1] .empty .empty) .empty)) (.node [12,8,8,6,6,6,5,3,3,2,1,1,1] (.node [12,8,8,6,6,6,5,3,2,2,2,1,1] (.node [12,8,8,6,6,6,5,2,2,2,2,2,1] .empty .empty) .empty) (.node [12,8,8,6,6,6,5,3,3,2,2,1] .empty .empty))) (.node [12,8,8,6,6,6,5,5,2,2,1,1] (.node [12,8,8,6,6,6,5,4,3,2,1,1] (.node [12,8,8,6,6,6,5,4,3,1,1,1,1] (.node [12,8,8,6,6,6,5,4,2,2,2,1] .empty .empty) .empty) (.node [12,8,8,6,6,6,5,5,2,1,1,1,1] (.node [12,8,8,6,6,6,5,4,4,1,1,1] .empty .empty) .empty)) (.node [12,8,8,6,6,6,6,2,2,2,2,2] (.node [12,8,8,6,6,6,6,2,2,2,2,1,1] (.node [12,8,8,6,6,6,5,5,3,1,1,1] .empty .empty) .empty) (.node [12,8,8,6,6,6,6,3,2,2,1,1,1] .empty .empty))))

def degreeTree62_354 : RowTree := (.node [12,8,8,6,6,6,4,2,2,2,2,2,2] degreeTree62_352 degreeTree62_353)

def degreeTree62_355 : RowTree := (.node [12,8,8,6,5,5,5,5,2,2,2,1,1] degreeTree62_351 degreeTree62_354)

def degreeTree62_356 : RowTree := (.node [12,8,8,7,5,5,4,4,4,2,1,1,1] (.node [12,8,8,6,6,6,6,5,1,1,1,1,1] (.node [12,8,8,6,6,6,6,4,2,1,1,1,1] (.node [12,8,8,6,6,6,6,3,3,2,1,1] (.node [12,8,8,6,6,6,6,3,3,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,6,6,6,6,4,3,1,1,1] (.node [12,8,8,6,6,6,6,4,2,2,1,1] .empty .empty) .empty)) (.node [12,8,8,7,5,4,4,4,4,2,2,1,1] (.node [12,8,8,6,6,6,6,6,1,1,1,1] (.node [12,8,8,6,6,6,6,5,2,1,1,1] .empty .empty) .empty) (.node [12,8,8,7,5,5,4,4,3,2,2,1,1] .empty .empty))) (.node [12,8,8,7,5,5,5,4,3,2,2,1] (.node [12,8,8,7,5,5,5,3,3,2,2,1,1] (.node [12,8,8,7,5,5,5,2,2,2,2,2,2] (.node [12,8,8,7,5,5,4,4,4,2,2,1] .empty .empty) .empty) (.node [12,8,8,7,5,5,5,4,3,2,1,1,1] (.node [12,8,8,7,5,5,5,4,2,2,2,1,1] .empty .empty) .empty)) (.node [12,8,8,7,5,5,5,5,2,2,1,1,1] (.node [12,8,8,7,5,5,5,4,4,2,1,1] (.node [12,8,8,7,5,5,5,4,4,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,7,5,5,5,5,2,2,2,1] .empty .empty))))

def degreeTree62_357 : RowTree := (.node [12,8,8,7,6,5,4,4,4,1,1,1,1] (.node [12,8,8,7,6,5,4,2,2,2,2,2,2] (.node [12,8,8,7,6,4,4,4,3,2,2,1,1] (.node [12,8,8,7,5,5,5,5,4,1,1,1] (.node [12,8,8,7,5,5,5,5,3,2,1,1] .empty .empty) .empty) (.node [12,8,8,7,6,4,4,4,4,2,2,1] (.node [12,8,8,7,6,4,4,4,4,2,1,1,1] .empty .empty) .empty)) (.node [12,8,8,7,6,5,4,4,3,2,1,1,1] (.node [12,8,8,7,6,5,4,4,2,2,2,1,1] (.node [12,8,8,7,6,5,4,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,7,6,5,4,4,3,2,2,1] .empty .empty))) (.node [12,8,8,7,6,5,5,4,2,2,1,1,1] (.node [12,8,8,7,6,5,5,3,2,2,2,1,1] (.node [12,8,8,7,6,5,5,2,2,2,2,2,1] (.node [12,8,8,7,6,5,4,4,4,2,1,1] .empty .empty) .empty) (.node [12,8,8,7,6,5,5,3,3,2,2,1] (.node [12,8,8,7,6,5,5,3,3,2,1,1,1] .empty .empty) .empty)) (.node [12,8,8,7,6,5,5,4,3,2,1,1] (.node [12,8,8,7,6,5,5,4,3,1,1,1,1] (.node [12,8,8,7,6,5,5,4,2,2,2,1] .empty .empty) .empty) (.node [12,8,8,7,6,5,5,4,4,1,1,1] .empty .empty))))

def degreeTree62_358 : RowTree := (.node [12,8,8,7,5,5,5,5,3,1,1,1,1] degreeTree62_356 degreeTree62_357)

def degreeTree62_359 : RowTree := (.node [12,8,8,7,6,6,4,4,3,1,1,1,1] (.node [12,8,8,7,6,6,4,3,2,2,2,1,1] (.node [12,8,8,7,6,6,3,2,2,2,2,2,2] (.node [12,8,8,7,6,5,5,5,3,1,1,1] (.node [12,8,8,7,6,5,5,5,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,7,6,6,4,2,2,2,2,2,1] (.node [12,8,8,7,6,6,3,3,3,2,2,1,1] .empty .empty) .empty)) (.node [12,8,8,7,6,6,4,4,2,2,1,1,1] (.node [12,8,8,7,6,6,4,3,3,2,2,1] (.node [12,8,8,7,6,6,4,3,3,2,1,1,1] .empty .empty) .empty) (.node [12,8,8,7,6,6,4,4,2,2,2,1] .empty .empty))) (.node [12,8,8,7,6,6,5,3,2,2,2,1] (.node [12,8,8,7,6,6,5,2,2,2,2,1,1] (.node [12,8,8,7,6,6,4,4,4,1,1,1] (.node [12,8,8,7,6,6,4,4,3,2,1,1] .empty .empty) .empty) (.node [12,8,8,7,6,6,5,3,2,2,1,1,1] (.node [12,8,8,7,6,6,5,2,2,2,2,2] .empty .empty) .empty)) (.node [12,8,8,7,6,6,5,4,2,1,1,1,1] (.node [12,8,8,7,6,6,5,3,3,2,1,1] (.node [12,8,8,7,6,6,5,3,3,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,7,6,6,5,4,2,2,1,1] .empty .empty))))

def degreeTree62_360 : RowTree := (.node [12,8,8,7,7,4,4,2,2,2,2,2,2] (.node [12,8,8,7,6,6,6,3,2,2,1,1] (.node [12,8,8,7,6,6,6,2,2,2,1,1,1] (.node [12,8,8,7,6,6,5,5,2,1,1,1] (.node [12,8,8,7,6,6,5,5,1,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,7,6,6,6,3,2,1,1,1,1] (.node [12,8,8,7,6,6,6,2,2,2,2,1] .empty .empty) .empty)) (.node [12,8,8,7,6,6,6,4,2,1,1,1] (.node [12,8,8,7,6,6,6,4,1,1,1,1,1] (.node [12,8,8,7,6,6,6,3,3,1,1,1] .empty .empty) .empty) (.node [12,8,8,7,6,6,6,5,1,1,1,1] .empty .empty))) (.node [12,8,8,7,7,4,4,4,4,2,1,1] (.node [12,8,8,7,7,4,4,4,3,2,1,1,1] (.node [12,8,8,7,7,4,4,4,2,2,2,1,1] (.node [12,8,8,7,7,4,4,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,7,7,4,4,4,4,1,1,1,1] (.node [12,8,8,7,7,4,4,4,3,2,2,1] .empty .empty) .empty)) (.node [12,8,8,7,7,5,4,2,2,2,2,2,1] (.node [12,8,8,7,7,5,3,3,3,2,2,1,1] (.node [12,8,8,7,7,5,3,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,8,8,7,7,5,4,3,2,2,2,1,1] .empty .empty))))

def degreeTree62_361 : RowTree := (.node [12,8,8,7,6,6,5,4,3,1,1,1] degreeTree62_359 degreeTree62_360)

def degreeTree62_362 : RowTree := (.node [12,8,8,7,6,5,5,5,2,1,1,1,1] degreeTree62_358 degreeTree62_361)

def degreeTree62_363 : RowTree := (.node [12,8,8,6,6,6,6,3,2,2,2,1] degreeTree62_355 degreeTree62_362)

def degreeTree62_364 : RowTree := (.node [12,8,8,7,7,5,5,3,3,1,1,1,1] (.node [12,8,8,7,7,5,4,4,4,1,1,1] (.node [12,8,8,7,7,5,4,4,2,2,2,1] (.node [12,8,8,7,7,5,4,4,2,2,1,1,1] (.node [12,8,8,7,7,5,4,3,3,2,2,1] .empty .empty) .empty) (.node [12,8,8,7,7,5,4,4,3,2,1,1] (.node [12,8,8,7,7,5,4,4,3,1,1,1,1] .empty .empty) .empty)) (.node [12,8,8,7,7,5,5,3,2,2,1,1,1] (.node [12,8,8,7,7,5,5,2,2,2,2,2] (.node [12,8,8,7,7,5,5,2,2,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,7,7,5,5,3,2,2,2,1] .empty .empty))) (.node [12,8,8,7,7,5,5,5,2,1,1,1] (.node [12,8,8,7,7,5,5,4,2,2,1,1] (.node [12,8,8,7,7,5,5,4,2,1,1,1,1] (.node [12,8,8,7,7,5,5,3,3,2,1,1] .empty .empty) .empty) (.node [12,8,8,7,7,5,5,5,1,1,1,1,1] (.node [12,8,8,7,7,5,5,4,3,1,1,1] .empty .empty) .empty)) (.node [12,8,8,7,7,6,3,3,2,2,2,1,1] (.node [12,8,8,7,7,6,3,2,2,2,2,2,1] (.node [12,8,8,7,7,6,2,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,8,8,7,7,6,3,3,3,2,1,1,1] .empty .empty))))

def degreeTree62_365 : RowTree := (.node [12,8,8,7,7,6,5,2,2,2,2,1] (.node [12,8,8,7,7,6,4,3,3,2,1,1] (.node [12,8,8,7,7,6,4,3,2,2,1,1,1] (.node [12,8,8,7,7,6,4,2,2,2,2,2] (.node [12,8,8,7,7,6,4,2,2,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,7,7,6,4,3,3,1,1,1,1] (.node [12,8,8,7,7,6,4,3,2,2,2,1] .empty .empty) .empty)) (.node [12,8,8,7,7,6,4,4,3,1,1,1] (.node [12,8,8,7,7,6,4,4,2,2,1,1] (.node [12,8,8,7,7,6,4,4,2,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,7,7,6,5,2,2,2,1,1,1] .empty .empty))) (.node [12,8,8,7,7,6,5,5,1,1,1,1] (.node [12,8,8,7,7,6,5,3,3,1,1,1] (.node [12,8,8,7,7,6,5,3,2,2,1,1] (.node [12,8,8,7,7,6,5,3,2,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,7,7,6,5,4,2,1,1,1] (.node [12,8,8,7,7,6,5,4,1,1,1,1,1] .empty .empty) .empty)) (.node [12,8,8,7,7,6,6,2,2,2,1,1] (.node [12,8,8,7,7,6,6,2,2,1,1,1,1] (.node [12,8,8,7,7,6,6,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,7,7,6,6,3,1,1,1,1,1] .empty .empty))))

def degreeTree62_366 : RowTree := (.node [12,8,8,7,7,6,3,3,3,2,2,1] degreeTree62_364 degreeTree62_365)

def degreeTree62_367 : RowTree := (.node [12,8,8,7,7,7,3,3,3,2,1,1] (.node [12,8,8,7,7,7,3,2,2,2,2,2] (.node [12,8,8,7,7,7,2,2,2,2,2,2,1] (.node [12,8,8,7,7,7,2,2,2,2,2,1,1,1] (.node [12,8,8,7,7,6,6,4,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,7,7,7,3,2,2,2,2,1,1] (.node [12,8,8,7,7,7,3,2,2,2,1,1,1,1] .empty .empty) .empty)) (.node [12,8,8,7,7,7,3,3,2,2,2,1] (.node [12,8,8,7,7,7,3,3,2,2,1,1,1] (.node [12,8,8,7,7,7,3,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,7,7,7,3,3,3,1,1,1,1] .empty .empty))) (.node [12,8,8,7,7,7,4,3,2,2,1,1] (.node [12,8,8,7,7,7,4,2,2,2,2,1] (.node [12,8,8,7,7,7,4,2,2,2,1,1,1] (.node [12,8,8,7,7,7,4,2,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,7,7,7,4,3,2,1,1,1,1] (.node [12,8,8,7,7,7,4,3,1,1,1,1,1,1] .empty .empty) .empty)) (.node [12,8,8,7,7,7,4,4,2,1,1,1] (.node [12,8,8,7,7,7,4,4,1,1,1,1,1] (.node [12,8,8,7,7,7,4,3,3,1,1,1] .empty .empty) .empty) (.node [12,8,8,7,7,7,5,2,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_368 : RowTree := (.node [12,8,8,8,5,4,4,4,3,2,2,1,1] (.node [12,8,8,7,7,7,6,2,1,1,1,1,1] (.node [12,8,8,7,7,7,5,3,2,1,1,1] (.node [12,8,8,7,7,7,5,3,1,1,1,1,1] (.node [12,8,8,7,7,7,5,2,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,7,7,7,6,1,1,1,1,1,1,1] (.node [12,8,8,7,7,7,5,4,1,1,1,1] .empty .empty) .empty)) (.node [12,8,8,7,7,7,7,1,1,1,1,1,1] (.node [12,8,8,7,7,7,6,3,1,1,1,1] (.node [12,8,8,7,7,7,6,2,2,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,4,4,4,4,4,2,2,1,1] .empty .empty))) (.node [12,8,8,8,5,5,4,4,3,2,1,1,1] (.node [12,8,8,8,5,5,4,2,2,2,2,2,2] (.node [12,8,8,8,5,4,4,4,4,2,2,1] (.node [12,8,8,8,5,4,4,4,4,2,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,5,5,4,4,2,2,2,1,1] (.node [12,8,8,8,5,5,4,3,3,2,2,1,1] .empty .empty) .empty)) (.node [12,8,8,8,5,5,4,4,4,2,1,1] (.node [12,8,8,8,5,5,4,4,4,1,1,1,1] (.node [12,8,8,8,5,5,4,4,3,2,2,1] .empty .empty) .empty) (.node [12,8,8,8,5,5,5,2,2,2,2,2,1] .empty .empty))))

def degreeTree62_369 : RowTree := (.node [12,8,8,7,7,7,5,2,2,1,1,1,1] degreeTree62_367 degreeTree62_368)

def degreeTree62_370 : RowTree := (.node [12,8,8,7,7,6,6,3,2,1,1,1] degreeTree62_366 degreeTree62_369)

def degreeTree62_371 : RowTree := (.node [12,8,8,8,6,4,4,2,2,2,2,2,2] (.node [12,8,8,8,5,5,5,4,3,2,1,1] (.node [12,8,8,8,5,5,5,4,2,2,1,1,1] (.node [12,8,8,8,5,5,5,3,3,2,2,1] (.node [12,8,8,8,5,5,5,3,3,2,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,5,5,5,4,3,1,1,1,1] (.node [12,8,8,8,5,5,5,4,2,2,2,1] .empty .empty) .empty)) (.node [12,8,8,8,5,5,5,5,2,2,1,1] (.node [12,8,8,8,5,5,5,5,2,1,1,1,1] (.node [12,8,8,8,5,5,5,4,4,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,5,5,5,5,3,1,1,1] .empty .empty))) (.node [12,8,8,8,6,4,4,4,4,2,1,1] (.node [12,8,8,8,6,4,4,4,3,2,1,1,1] (.node [12,8,8,8,6,4,4,4,2,2,2,1,1] (.node [12,8,8,8,6,4,4,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,8,6,4,4,4,4,1,1,1,1] (.node [12,8,8,8,6,4,4,4,3,2,2,1] .empty .empty) .empty)) (.node [12,8,8,8,6,5,4,2,2,2,2,2,1] (.node [12,8,8,8,6,5,3,3,3,2,2,1,1] (.node [12,8,8,8,6,5,3,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,8,8,8,6,5,4,3,2,2,2,1,1] .empty .empty))))

def degreeTree62_372 : RowTree := (.node [12,8,8,8,6,5,5,3,3,1,1,1,1] (.node [12,8,8,8,6,5,4,4,4,1,1,1] (.node [12,8,8,8,6,5,4,4,2,2,2,1] (.node [12,8,8,8,6,5,4,4,2,2,1,1,1] (.node [12,8,8,8,6,5,4,3,3,2,2,1] .empty .empty) .empty) (.node [12,8,8,8,6,5,4,4,3,2,1,1] (.node [12,8,8,8,6,5,4,4,3,1,1,1,1] .empty .empty) .empty)) (.node [12,8,8,8,6,5,5,3,2,2,1,1,1] (.node [12,8,8,8,6,5,5,2,2,2,2,2] (.node [12,8,8,8,6,5,5,2,2,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,8,6,5,5,3,2,2,2,1] .empty .empty))) (.node [12,8,8,8,6,5,5,5,2,1,1,1] (.node [12,8,8,8,6,5,5,4,2,2,1,1] (.node [12,8,8,8,6,5,5,4,2,1,1,1,1] (.node [12,8,8,8,6,5,5,3,3,2,1,1] .empty .empty) .empty) (.node [12,8,8,8,6,5,5,5,1,1,1,1,1] (.node [12,8,8,8,6,5,5,4,3,1,1,1] .empty .empty) .empty)) (.node [12,8,8,8,6,6,3,3,2,2,2,1,1] (.node [12,8,8,8,6,6,3,2,2,2,2,2,1] (.node [12,8,8,8,6,6,2,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,8,8,8,6,6,3,3,3,2,1,1,1] .empty .empty))))

def degreeTree62_373 : RowTree := (.node [12,8,8,8,6,5,4,3,3,2,1,1,1] degreeTree62_371 degreeTree62_372)

def degreeTree62_374 : RowTree := (.node [12,8,8,8,6,6,5,2,2,2,2,1] (.node [12,8,8,8,6,6,4,3,3,2,1,1] (.node [12,8,8,8,6,6,4,3,2,2,1,1,1] (.node [12,8,8,8,6,6,4,2,2,2,2,2] (.node [12,8,8,8,6,6,4,2,2,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,8,6,6,4,3,3,1,1,1,1] (.node [12,8,8,8,6,6,4,3,2,2,2,1] .empty .empty) .empty)) (.node [12,8,8,8,6,6,4,4,3,1,1,1] (.node [12,8,8,8,6,6,4,4,2,2,1,1] (.node [12,8,8,8,6,6,4,4,2,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,6,6,5,2,2,2,1,1,1] .empty .empty))) (.node [12,8,8,8,6,6,5,5,1,1,1,1] (.node [12,8,8,8,6,6,5,3,3,1,1,1] (.node [12,8,8,8,6,6,5,3,2,2,1,1] (.node [12,8,8,8,6,6,5,3,2,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,6,6,5,4,2,1,1,1] (.node [12,8,8,8,6,6,5,4,1,1,1,1,1] .empty .empty) .empty)) (.node [12,8,8,8,6,6,6,2,2,2,1,1] (.node [12,8,8,8,6,6,6,2,2,1,1,1,1] (.node [12,8,8,8,6,6,6,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,6,6,6,3,1,1,1,1,1] .empty .empty))))

def degreeTree62_375 : RowTree := (.node [12,8,8,8,7,4,4,4,3,2,1,1] (.node [12,8,8,8,7,4,4,3,3,2,1,1,1] (.node [12,8,8,8,7,4,3,3,3,2,2,1,1] (.node [12,8,8,8,7,4,3,2,2,2,2,2,2] (.node [12,8,8,8,6,6,6,4,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,7,4,4,3,2,2,2,1,1] (.node [12,8,8,8,7,4,4,2,2,2,2,2,1] .empty .empty) .empty)) (.node [12,8,8,8,7,4,4,4,2,2,2,1] (.node [12,8,8,8,7,4,4,4,2,2,1,1,1] (.node [12,8,8,8,7,4,4,3,3,2,2,1] .empty .empty) .empty) (.node [12,8,8,8,7,4,4,4,3,1,1,1,1] .empty .empty))) (.node [12,8,8,8,7,5,3,3,3,2,1,1,1] (.node [12,8,8,8,7,5,3,2,2,2,2,2,1] (.node [12,8,8,8,7,5,2,2,2,2,2,2,2] (.node [12,8,8,8,7,4,4,4,4,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,7,5,3,3,2,2,2,1,1] .empty .empty)) (.node [12,8,8,8,7,5,4,2,2,2,2,2] (.node [12,8,8,8,7,5,4,2,2,2,2,1,1] (.node [12,8,8,8,7,5,3,3,3,2,2,1] .empty .empty) .empty) (.node [12,8,8,8,7,5,4,3,2,2,1,1,1] .empty .empty))))

def degreeTree62_376 : RowTree := (.node [12,8,8,8,6,6,6,3,2,1,1,1] degreeTree62_374 degreeTree62_375)

def degreeTree62_377 : RowTree := (.node [12,8,8,8,6,6,3,3,3,2,2,1] degreeTree62_373 degreeTree62_376)

def degreeTree62_378 : RowTree := (.node [12,8,8,8,5,5,5,3,2,2,2,1,1] degreeTree62_370 degreeTree62_377)

def degreeTree62_379 : RowTree := (.node [12,8,8,7,7,5,4,3,3,2,1,1,1] degreeTree62_363 degreeTree62_378)

def degreeTree62_380 : RowTree := (.node [12,8,7,7,7,6,6,4,2,1,1,1] degreeTree62_348 degreeTree62_379)

def degreeTree62_381 : RowTree := (.node [12,7,7,6,5,5,5,5,5,2,1,1,1] degreeTree62_317 degreeTree62_380)

def degreeTree62_382 : RowTree := (.node [12,8,8,8,7,5,5,4,1,1,1,1,1] (.node [12,8,8,8,7,5,5,2,2,2,1,1,1] (.node [12,8,8,8,7,5,4,4,2,1,1,1,1] (.node [12,8,8,8,7,5,4,3,3,2,1,1] (.node [12,8,8,8,7,5,4,3,3,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,7,5,4,4,3,1,1,1] (.node [12,8,8,8,7,5,4,4,2,2,1,1] .empty .empty) .empty)) (.node [12,8,8,8,7,5,5,3,2,2,1,1] (.node [12,8,8,8,7,5,5,3,2,1,1,1,1] (.node [12,8,8,8,7,5,5,2,2,2,2,1] .empty .empty) .empty) (.node [12,8,8,8,7,5,5,3,3,1,1,1] .empty .empty))) (.node [12,8,8,8,7,6,3,2,2,2,2,1,1] (.node [12,8,8,8,7,6,2,2,2,2,2,1,1,1] (.node [12,8,8,8,7,5,5,5,1,1,1,1] (.node [12,8,8,8,7,5,5,4,2,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,7,6,3,2,2,2,1,1,1,1] (.node [12,8,8,8,7,6,2,2,2,2,2,2,1] .empty .empty) .empty)) (.node [12,8,8,8,7,6,3,3,2,2,1,1,1] (.node [12,8,8,8,7,6,3,3,2,1,1,1,1,1] (.node [12,8,8,8,7,6,3,2,2,2,2,2] .empty .empty) .empty) (.node [12,8,8,8,7,6,3,3,2,2,2,1] .empty .empty))))

def degreeTree62_383 : RowTree := (.node [12,8,8,8,7,6,5,2,1,1,1,1,1,1] (.node [12,8,8,8,7,6,4,3,2,1,1,1,1] (.node [12,8,8,8,7,6,4,2,2,2,1,1,1] (.node [12,8,8,8,7,6,4,2,2,1,1,1,1,1] (.node [12,8,8,8,7,6,3,3,3,2,1,1] .empty .empty) .empty) (.node [12,8,8,8,7,6,4,3,1,1,1,1,1,1] (.node [12,8,8,8,7,6,4,2,2,2,2,1] .empty .empty) .empty)) (.node [12,8,8,8,7,6,4,4,1,1,1,1,1] (.node [12,8,8,8,7,6,4,3,3,1,1,1] (.node [12,8,8,8,7,6,4,3,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,8,7,6,4,4,2,1,1,1] .empty .empty))) (.node [12,8,8,8,7,6,6,1,1,1,1,1,1,1] (.node [12,8,8,8,7,6,5,3,1,1,1,1,1] (.node [12,8,8,8,7,6,5,2,2,2,1,1] (.node [12,8,8,8,7,6,5,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,7,6,5,4,1,1,1,1] (.node [12,8,8,8,7,6,5,3,2,1,1,1] .empty .empty) .empty)) (.node [12,8,8,8,7,7,2,2,2,2,1,1,1,1] (.node [12,8,8,8,7,6,6,2,2,1,1,1] (.node [12,8,8,8,7,6,6,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,7,7,2,2,2,2,2,1,1] .empty .empty))))

def degreeTree62_384 : RowTree := (.node [12,8,8,8,7,6,3,3,3,1,1,1,1] degreeTree62_382 degreeTree62_383)

def degreeTree62_385 : RowTree := (.node [12,8,8,8,7,7,4,3,1,1,1,1,1] (.node [12,8,8,8,7,7,3,3,2,2,1,1] (.node [12,8,8,8,7,7,3,2,2,2,2,1] (.node [12,8,8,8,7,7,3,2,2,2,1,1,1] (.node [12,8,8,8,7,7,3,2,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,7,7,3,3,2,1,1,1,1] (.node [12,8,8,8,7,7,3,3,1,1,1,1,1,1] .empty .empty) .empty)) (.node [12,8,8,8,7,7,4,2,2,1,1,1,1] (.node [12,8,8,8,7,7,4,2,1,1,1,1,1,1] (.node [12,8,8,8,7,7,3,3,3,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,7,7,4,2,2,2,1,1] .empty .empty))) (.node [12,8,8,8,8,3,3,2,2,2,2,2,2] (.node [12,8,8,8,7,7,5,2,1,1,1,1,1] (.node [12,8,8,8,7,7,5,1,1,1,1,1,1,1] (.node [12,8,8,8,7,7,4,3,2,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,7,7,6,1,1,1,1,1,1] (.node [12,8,8,8,7,7,5,2,2,1,1,1] .empty .empty) .empty)) (.node [12,8,8,8,8,4,3,2,2,2,2,1,1,1] (.node [12,8,8,8,8,4,2,2,2,2,2,2,2] (.node [12,8,8,8,8,3,3,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,8,8,4,3,2,2,2,2,2,1] .empty .empty))))

def degreeTree62_386 : RowTree := (.node [12,8,8,8,8,4,4,3,3,2,1,1] (.node [12,8,8,8,8,4,4,2,2,2,2,2] (.node [12,8,8,8,8,4,3,3,3,2,2,1] (.node [12,8,8,8,8,4,3,3,3,2,1,1,1] (.node [12,8,8,8,8,4,3,3,3,1,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,8,4,4,2,2,2,2,1,1] (.node [12,8,8,8,8,4,4,2,2,2,1,1,1,1] .empty .empty) .empty)) (.node [12,8,8,8,8,4,4,3,2,2,2,1] (.node [12,8,8,8,8,4,4,3,2,2,1,1,1] (.node [12,8,8,8,8,4,4,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,8,4,4,3,3,1,1,1,1] .empty .empty))) (.node [12,8,8,8,8,5,2,2,2,2,2,2,1] (.node [12,8,8,8,8,4,4,4,2,2,1,1] (.node [12,8,8,8,8,4,4,4,2,1,1,1,1] (.node [12,8,8,8,8,4,4,4,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,8,5,2,2,2,2,2,1,1,1] (.node [12,8,8,8,8,4,4,4,3,1,1,1] .empty .empty) .empty)) (.node [12,8,8,8,8,5,3,2,2,2,2,2] (.node [12,8,8,8,8,5,3,2,2,2,2,1,1] (.node [12,8,8,8,8,5,3,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,8,5,3,3,2,1,1,1,1,1] .empty .empty))))

def degreeTree62_387 : RowTree := (.node [12,8,8,8,8,4,3,3,2,2,2,1,1] degreeTree62_385 degreeTree62_386)

def degreeTree62_388 : RowTree := (.node [12,8,8,8,7,7,2,2,2,2,2,2] degreeTree62_384 degreeTree62_387)

def degreeTree62_389 : RowTree := (.node [12,8,8,8,8,5,4,4,1,1,1,1,1] (.node [12,8,8,8,8,5,4,2,2,2,2,1] (.node [12,8,8,8,8,5,3,3,3,2,1,1] (.node [12,8,8,8,8,5,3,3,3,1,1,1,1] (.node [12,8,8,8,8,5,3,3,2,2,2,1] .empty .empty) .empty) (.node [12,8,8,8,8,5,4,2,2,2,1,1,1] (.node [12,8,8,8,8,5,4,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [12,8,8,8,8,5,4,3,2,2,1,1] (.node [12,8,8,8,8,5,4,3,2,1,1,1,1] (.node [12,8,8,8,8,5,4,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,8,5,4,3,3,1,1,1] .empty .empty))) (.node [12,8,8,8,8,5,5,3,2,1,1,1] (.node [12,8,8,8,8,5,5,2,2,1,1,1,1] (.node [12,8,8,8,8,5,5,2,1,1,1,1,1,1] (.node [12,8,8,8,8,5,4,4,2,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,8,5,5,3,1,1,1,1,1] (.node [12,8,8,8,8,5,5,2,2,2,1,1] .empty .empty) .empty)) (.node [12,8,8,8,8,6,2,2,2,2,2,2] (.node [12,8,8,8,8,6,2,2,2,2,2,1,1] (.node [12,8,8,8,8,6,2,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,8,6,3,2,2,1,1,1,1,1] .empty .empty))))

def degreeTree62_390 : RowTree := (.node [12,8,8,8,8,6,5,1,1,1,1,1,1,1] (.node [12,8,8,8,8,6,4,2,1,1,1,1,1,1] (.node [12,8,8,8,8,6,3,3,2,1,1,1,1] (.node [12,8,8,8,8,6,3,3,1,1,1,1,1,1] (.node [12,8,8,8,8,6,3,2,2,2,2,1] .empty .empty) .empty) (.node [12,8,8,8,8,6,3,3,3,1,1,1] (.node [12,8,8,8,8,6,3,3,2,2,1,1] .empty .empty) .empty)) (.node [12,8,8,8,8,6,4,3,1,1,1,1,1] (.node [12,8,8,8,8,6,4,2,2,2,1,1] (.node [12,8,8,8,8,6,4,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,8,6,4,3,2,1,1,1] .empty .empty))) (.node [12,8,8,8,8,7,2,2,2,2,2,1] (.node [12,8,8,8,8,6,6,1,1,1,1,1,1] (.node [12,8,8,8,8,6,5,2,2,1,1,1] (.node [12,8,8,8,8,6,5,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,8,7,2,2,2,2,1,1,1] (.node [12,8,8,8,8,7,2,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [12,8,8,8,8,7,3,2,2,2,1,1] (.node [12,8,8,8,8,7,3,2,2,1,1,1,1] (.node [12,8,8,8,8,7,3,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,8,7,3,3,1,1,1,1,1] .empty .empty))))

def degreeTree62_391 : RowTree := (.node [12,8,8,8,8,6,3,2,2,2,1,1,1] degreeTree62_389 degreeTree62_390)

def degreeTree62_392 : RowTree := (.node [12,8,8,8,8,8,4,1,1,1,1,1,1] (.node [12,8,8,8,8,8,2,2,2,1,1,1,1] (.node [12,8,8,8,8,7,4,2,2,1,1,1] (.node [12,8,8,8,8,7,4,2,1,1,1,1,1] (.node [12,8,8,8,8,7,4,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,8,8,8,8,8,2,2,1,1,1,1,1,1] (.node [12,8,8,8,8,7,5,1,1,1,1,1,1] .empty .empty) .empty)) (.node [12,8,8,8,8,8,3,2,1,1,1,1,1] (.node [12,8,8,8,8,8,3,1,1,1,1,1,1,1] (.node [12,8,8,8,8,8,2,2,2,2,1,1] .empty .empty) .empty) (.node [12,8,8,8,8,8,3,2,2,1,1,1] .empty .empty))) (.node [12,9,6,6,5,5,5,5,3,2,2,1,1] (.node [12,9,6,5,5,5,5,5,5,2,1,1,1] (.node [12,9,6,5,5,5,5,5,4,2,2,1,1] (.node [12,9,5,5,5,5,5,5,5,2,2,1,1] .empty .empty) .empty) (.node [12,9,6,6,5,5,5,4,4,2,2,1,1] (.node [12,9,6,5,5,5,5,5,5,2,2,1] .empty .empty) .empty)) (.node [12,9,6,6,5,5,5,5,5,1,1,1,1] (.node [12,9,6,6,5,5,5,5,4,2,2,1] (.node [12,9,6,6,5,5,5,5,4,2,1,1,1] .empty .empty) .empty) (.node [12,9,6,6,5,5,5,5,5,2,1,1] .empty .empty))))

def degreeTree62_393 : RowTree := (.node [12,9,6,6,6,6,4,4,4,2,1,1,1] (.node [12,9,6,6,6,5,5,5,3,2,2,1] (.node [12,9,6,6,6,5,5,4,4,2,2,1] (.node [12,9,6,6,6,5,5,4,4,2,1,1,1] (.node [12,9,6,6,6,5,5,4,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,6,6,6,5,5,5,3,2,1,1,1] (.node [12,9,6,6,6,5,5,5,2,2,2,1,1] .empty .empty) .empty)) (.node [12,9,6,6,6,5,5,5,5,1,1,1] (.node [12,9,6,6,6,5,5,5,4,2,1,1] (.node [12,9,6,6,6,5,5,5,4,1,1,1,1] .empty .empty) .empty) (.node [12,9,6,6,6,6,4,4,3,2,2,1,1] .empty .empty))) (.node [12,9,6,6,6,6,5,4,3,2,2,1] (.node [12,9,6,6,6,6,5,3,3,2,2,1,1] (.node [12,9,6,6,6,6,5,2,2,2,2,2,2] (.node [12,9,6,6,6,6,4,4,4,2,2,1] .empty .empty) .empty) (.node [12,9,6,6,6,6,5,4,3,2,1,1,1] (.node [12,9,6,6,6,6,5,4,2,2,2,1,1] .empty .empty) .empty)) (.node [12,9,6,6,6,6,5,5,2,2,1,1,1] (.node [12,9,6,6,6,6,5,4,4,2,1,1] (.node [12,9,6,6,6,6,5,4,4,1,1,1,1] .empty .empty) .empty) (.node [12,9,6,6,6,6,5,5,2,2,2,1] .empty .empty))))

def degreeTree62_394 : RowTree := (.node [12,9,6,6,6,5,4,4,4,2,2,1,1] degreeTree62_392 degreeTree62_393)

def degreeTree62_395 : RowTree := (.node [12,8,8,8,8,7,3,3,2,1,1,1] degreeTree62_391 degreeTree62_394)

def degreeTree62_396 : RowTree := (.node [12,8,8,8,8,5,3,3,2,2,1,1,1] degreeTree62_388 degreeTree62_395)

def degreeTree62_397 : RowTree := (.node [12,9,6,6,6,6,6,4,4,1,1,1] (.node [12,9,6,6,6,6,6,3,3,2,2,1] (.node [12,9,6,6,6,6,6,2,2,2,2,2,1] (.node [12,9,6,6,6,6,5,5,4,1,1,1] (.node [12,9,6,6,6,6,5,5,3,2,1,1] .empty .empty) .empty) (.node [12,9,6,6,6,6,6,3,3,2,1,1,1] (.node [12,9,6,6,6,6,6,3,2,2,2,1,1] .empty .empty) .empty)) (.node [12,9,6,6,6,6,6,4,3,1,1,1,1] (.node [12,9,6,6,6,6,6,4,2,2,2,1] (.node [12,9,6,6,6,6,6,4,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,6,6,6,6,6,4,3,2,1,1] .empty .empty))) (.node [12,9,7,5,5,5,5,4,4,2,2,1,1] (.node [12,9,6,6,6,6,6,5,3,1,1,1] (.node [12,9,6,6,6,6,6,5,2,2,1,1] (.node [12,9,6,6,6,6,6,5,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,6,6,6,6,6,6,2,1,1,1] (.node [12,9,6,6,6,6,6,6,1,1,1,1,1] .empty .empty) .empty)) (.node [12,9,7,5,5,5,5,5,4,2,2,1] (.node [12,9,7,5,5,5,5,5,4,2,1,1,1] (.node [12,9,7,5,5,5,5,5,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,7,5,5,5,5,5,5,1,1,1,1] .empty .empty))))

def degreeTree62_398 : RowTree := (.node [12,9,7,6,6,4,4,4,4,2,2,1,1] (.node [12,9,7,6,5,5,5,5,3,2,1,1,1] (.node [12,9,7,6,5,5,5,4,4,2,1,1,1] (.node [12,9,7,6,5,5,5,4,3,2,2,1,1] (.node [12,9,7,6,5,5,4,4,4,2,2,1,1] .empty .empty) .empty) (.node [12,9,7,6,5,5,5,5,2,2,2,1,1] (.node [12,9,7,6,5,5,5,4,4,2,2,1] .empty .empty) .empty)) (.node [12,9,7,6,5,5,5,5,4,2,1,1] (.node [12,9,7,6,5,5,5,5,4,1,1,1,1] (.node [12,9,7,6,5,5,5,5,3,2,2,1] .empty .empty) .empty) (.node [12,9,7,6,5,5,5,5,5,1,1,1] .empty .empty))) (.node [12,9,7,6,6,5,5,4,2,2,2,1,1] (.node [12,9,7,6,6,5,4,4,4,2,2,1] (.node [12,9,7,6,6,5,4,4,4,2,1,1,1] (.node [12,9,7,6,6,5,4,4,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,7,6,6,5,5,3,3,2,2,1,1] (.node [12,9,7,6,6,5,5,2,2,2,2,2,2] .empty .empty) .empty)) (.node [12,9,7,6,6,5,5,4,4,1,1,1,1] (.node [12,9,7,6,6,5,5,4,3,2,2,1] (.node [12,9,7,6,6,5,5,4,3,2,1,1,1] .empty .empty) .empty) (.node [12,9,7,6,6,5,5,4,4,2,1,1] .empty .empty))))

def degreeTree62_399 : RowTree := (.node [12,9,7,5,5,5,5,5,5,2,1,1] degreeTree62_397 degreeTree62_398)

def degreeTree62_400 : RowTree := (.node [12,9,7,6,6,6,4,4,4,2,1,1] (.node [12,9,7,6,6,6,4,3,3,2,2,1,1] (.node [12,9,7,6,6,5,5,5,3,2,1,1] (.node [12,9,7,6,6,5,5,5,3,1,1,1,1] (.node [12,9,7,6,6,5,5,5,2,2,2,1] .empty .empty) .empty) (.node [12,9,7,6,6,6,4,2,2,2,2,2,2] (.node [12,9,7,6,6,5,5,5,4,1,1,1] .empty .empty) .empty)) (.node [12,9,7,6,6,6,4,4,3,2,2,1] (.node [12,9,7,6,6,6,4,4,3,2,1,1,1] (.node [12,9,7,6,6,6,4,4,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,7,6,6,6,4,4,4,1,1,1,1] .empty .empty))) (.node [12,9,7,6,6,6,5,4,2,2,2,1] (.node [12,9,7,6,6,6,5,3,3,2,1,1,1] (.node [12,9,7,6,6,6,5,3,2,2,2,1,1] (.node [12,9,7,6,6,6,5,2,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,7,6,6,6,5,4,2,2,1,1,1] (.node [12,9,7,6,6,6,5,3,3,2,2,1] .empty .empty) .empty)) (.node [12,9,7,6,6,6,5,4,4,1,1,1] (.node [12,9,7,6,6,6,5,4,3,2,1,1] (.node [12,9,7,6,6,6,5,4,3,1,1,1,1] .empty .empty) .empty) (.node [12,9,7,6,6,6,5,5,2,1,1,1,1] .empty .empty))))

def degreeTree62_401 : RowTree := (.node [12,9,7,6,6,6,6,5,1,1,1,1,1] (.node [12,9,7,6,6,6,6,3,3,1,1,1,1] (.node [12,9,7,6,6,6,6,2,2,2,2,2] (.node [12,9,7,6,6,6,6,2,2,2,2,1,1] (.node [12,9,7,6,6,6,5,5,3,1,1,1] .empty .empty) .empty) (.node [12,9,7,6,6,6,6,3,2,2,2,1] (.node [12,9,7,6,6,6,6,3,2,2,1,1,1] .empty .empty) .empty)) (.node [12,9,7,6,6,6,6,4,2,2,1,1] (.node [12,9,7,6,6,6,6,4,2,1,1,1,1] (.node [12,9,7,6,6,6,6,3,3,2,1,1] .empty .empty) .empty) (.node [12,9,7,6,6,6,6,4,3,1,1,1] .empty .empty))) (.node [12,9,7,7,5,5,5,2,2,2,2,2,2] (.node [12,9,7,7,5,5,4,4,3,2,2,1,1] (.node [12,9,7,7,5,4,4,4,4,2,2,1,1] (.node [12,9,7,6,6,6,6,5,2,1,1,1] .empty .empty) .empty) (.node [12,9,7,7,5,5,4,4,4,2,2,1] (.node [12,9,7,7,5,5,4,4,4,2,1,1,1] .empty .empty) .empty)) (.node [12,9,7,7,5,5,5,4,3,2,1,1,1] (.node [12,9,7,7,5,5,5,4,2,2,2,1,1] (.node [12,9,7,7,5,5,5,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,7,7,5,5,5,4,3,2,2,1] .empty .empty))))

def degreeTree62_402 : RowTree := (.node [12,9,7,6,6,6,5,5,2,2,1,1] degreeTree62_400 degreeTree62_401)

def degreeTree62_403 : RowTree := (.node [12,9,7,6,6,5,5,5,2,2,1,1,1] degreeTree62_399 degreeTree62_402)

def degreeTree62_404 : RowTree := (.node [12,9,7,7,6,5,4,3,3,2,2,1,1] (.node [12,9,7,7,5,5,5,5,4,1,1,1] (.node [12,9,7,7,5,5,5,5,2,2,2,1] (.node [12,9,7,7,5,5,5,5,2,2,1,1,1] (.node [12,9,7,7,5,5,5,4,4,2,1,1] .empty .empty) .empty) (.node [12,9,7,7,5,5,5,5,3,2,1,1] (.node [12,9,7,7,5,5,5,5,3,1,1,1,1] .empty .empty) .empty)) (.node [12,9,7,7,6,4,4,4,4,2,2,1] (.node [12,9,7,7,6,4,4,4,4,2,1,1,1] (.node [12,9,7,7,6,4,4,4,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,7,7,6,5,4,2,2,2,2,2,2] .empty .empty))) (.node [12,9,7,7,6,5,5,2,2,2,2,2,1] (.node [12,9,7,7,6,5,4,4,3,2,2,1] (.node [12,9,7,7,6,5,4,4,3,2,1,1,1] (.node [12,9,7,7,6,5,4,4,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,7,7,6,5,4,4,4,2,1,1] (.node [12,9,7,7,6,5,4,4,4,1,1,1,1] .empty .empty) .empty)) (.node [12,9,7,7,6,5,5,3,3,2,2,1] (.node [12,9,7,7,6,5,5,3,3,2,1,1,1] (.node [12,9,7,7,6,5,5,3,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,7,7,6,5,5,4,2,2,1,1,1] .empty .empty))))

def degreeTree62_405 : RowTree := (.node [12,9,7,7,6,6,4,3,3,2,1,1,1] (.node [12,9,7,7,6,5,5,5,3,1,1,1] (.node [12,9,7,7,6,5,5,4,4,1,1,1] (.node [12,9,7,7,6,5,5,4,3,2,1,1] (.node [12,9,7,7,6,5,5,4,3,1,1,1,1] .empty .empty) .empty) (.node [12,9,7,7,6,5,5,5,2,2,1,1] (.node [12,9,7,7,6,5,5,5,2,1,1,1,1] .empty .empty) .empty)) (.node [12,9,7,7,6,6,4,2,2,2,2,2,1] (.node [12,9,7,7,6,6,3,3,3,2,2,1,1] (.node [12,9,7,7,6,6,3,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,9,7,7,6,6,4,3,2,2,2,1,1] .empty .empty))) (.node [12,9,7,7,6,6,4,4,4,1,1,1] (.node [12,9,7,7,6,6,4,4,2,2,2,1] (.node [12,9,7,7,6,6,4,4,2,2,1,1,1] (.node [12,9,7,7,6,6,4,3,3,2,2,1] .empty .empty) .empty) (.node [12,9,7,7,6,6,4,4,3,2,1,1] (.node [12,9,7,7,6,6,4,4,3,1,1,1,1] .empty .empty) .empty)) (.node [12,9,7,7,6,6,5,3,2,2,1,1,1] (.node [12,9,7,7,6,6,5,2,2,2,2,2] (.node [12,9,7,7,6,6,5,2,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,7,7,6,6,5,3,2,2,2,1] .empty .empty))))

def degreeTree62_406 : RowTree := (.node [12,9,7,7,6,5,5,4,2,2,2,1] degreeTree62_404 degreeTree62_405)

def degreeTree62_407 : RowTree := (.node [12,9,7,7,6,6,6,3,3,1,1,1] (.node [12,9,7,7,6,6,5,5,2,1,1,1] (.node [12,9,7,7,6,6,5,4,2,2,1,1] (.node [12,9,7,7,6,6,5,4,2,1,1,1,1] (.node [12,9,7,7,6,6,5,3,3,2,1,1] .empty .empty) .empty) (.node [12,9,7,7,6,6,5,5,1,1,1,1,1] (.node [12,9,7,7,6,6,5,4,3,1,1,1] .empty .empty) .empty)) (.node [12,9,7,7,6,6,6,3,2,1,1,1,1] (.node [12,9,7,7,6,6,6,2,2,2,2,1] (.node [12,9,7,7,6,6,6,2,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,7,7,6,6,6,3,2,2,1,1] .empty .empty))) (.node [12,9,7,7,7,4,4,4,3,2,1,1,1] (.node [12,9,7,7,7,4,4,2,2,2,2,2,2] (.node [12,9,7,7,6,6,6,4,2,1,1,1] (.node [12,9,7,7,6,6,6,4,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,7,7,7,4,4,4,2,2,2,1,1] (.node [12,9,7,7,7,4,4,3,3,2,2,1,1] .empty .empty) .empty)) (.node [12,9,7,7,7,4,4,4,4,2,1,1] (.node [12,9,7,7,7,4,4,4,4,1,1,1,1] (.node [12,9,7,7,7,4,4,4,3,2,2,1] .empty .empty) .empty) (.node [12,9,7,7,7,5,3,2,2,2,2,2,2] .empty .empty))))

def degreeTree62_408 : RowTree := (.node [12,9,7,7,7,5,5,2,2,2,2,2] (.node [12,9,7,7,7,5,4,4,2,2,2,1] (.node [12,9,7,7,7,5,4,3,3,2,1,1,1] (.node [12,9,7,7,7,5,4,3,2,2,2,1,1] (.node [12,9,7,7,7,5,4,2,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,7,7,7,5,4,4,2,2,1,1,1] (.node [12,9,7,7,7,5,4,3,3,2,2,1] .empty .empty) .empty)) (.node [12,9,7,7,7,5,4,4,4,1,1,1] (.node [12,9,7,7,7,5,4,4,3,2,1,1] (.node [12,9,7,7,7,5,4,4,3,1,1,1,1] .empty .empty) .empty) (.node [12,9,7,7,7,5,5,2,2,2,2,1,1] .empty .empty))) (.node [12,9,7,7,7,5,5,4,2,1,1,1,1] (.node [12,9,7,7,7,5,5,3,3,1,1,1,1] (.node [12,9,7,7,7,5,5,3,2,2,2,1] (.node [12,9,7,7,7,5,5,3,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,7,7,7,5,5,3,3,2,1,1] .empty .empty)) (.node [12,9,7,7,7,5,5,5,1,1,1,1,1] (.node [12,9,7,7,7,5,5,4,3,1,1,1] (.node [12,9,7,7,7,5,5,4,2,2,1,1] .empty .empty) .empty) (.node [12,9,7,7,7,5,5,5,2,1,1,1] .empty .empty))))

def degreeTree62_409 : RowTree := (.node [12,9,7,7,7,5,3,3,3,2,2,1,1] degreeTree62_407 degreeTree62_408)

def degreeTree62_410 : RowTree := (.node [12,9,7,7,6,6,5,3,3,1,1,1,1] degreeTree62_406 degreeTree62_409)

def degreeTree62_411 : RowTree := (.node [12,9,7,7,5,5,5,4,4,1,1,1,1] degreeTree62_403 degreeTree62_410)

def degreeTree62_412 : RowTree := (.node [12,9,6,6,6,6,5,5,3,1,1,1,1] degreeTree62_396 degreeTree62_411)

def degreeTree62_413 : RowTree := (.node [12,9,7,7,7,6,4,4,2,1,1,1,1] (.node [12,9,7,7,7,6,4,2,2,2,2,2] (.node [12,9,7,7,7,6,3,3,3,2,1,1,1] (.node [12,9,7,7,7,6,3,3,2,2,2,1,1] (.node [12,9,7,7,7,6,3,2,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,7,7,7,6,4,2,2,2,2,1,1] (.node [12,9,7,7,7,6,3,3,3,2,2,1] .empty .empty) .empty)) (.node [12,9,7,7,7,6,4,3,3,1,1,1,1] (.node [12,9,7,7,7,6,4,3,2,2,2,1] (.node [12,9,7,7,7,6,4,3,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,7,7,7,6,4,3,3,2,1,1] .empty .empty))) (.node [12,9,7,7,7,6,5,3,2,2,1,1] (.node [12,9,7,7,7,6,5,2,2,2,1,1,1] (.node [12,9,7,7,7,6,4,4,3,1,1,1] (.node [12,9,7,7,7,6,4,4,2,2,1,1] .empty .empty) .empty) (.node [12,9,7,7,7,6,5,3,2,1,1,1,1] (.node [12,9,7,7,7,6,5,2,2,2,2,1] .empty .empty) .empty)) (.node [12,9,7,7,7,6,5,4,2,1,1,1] (.node [12,9,7,7,7,6,5,4,1,1,1,1,1] (.node [12,9,7,7,7,6,5,3,3,1,1,1] .empty .empty) .empty) (.node [12,9,7,7,7,6,6,2,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_414 : RowTree := (.node [12,9,7,7,7,7,3,3,2,2,2,1] (.node [12,9,7,7,7,7,3,2,2,2,1,1,1,1] (.node [12,9,7,7,7,6,6,3,2,1,1,1] (.node [12,9,7,7,7,6,6,3,1,1,1,1,1] (.node [12,9,7,7,7,6,6,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,7,7,7,7,2,2,2,2,2,2,1] (.node [12,9,7,7,7,7,2,2,2,2,2,1,1,1] .empty .empty) .empty)) (.node [12,9,7,7,7,7,3,3,2,1,1,1,1,1] (.node [12,9,7,7,7,7,3,2,2,2,2,2] (.node [12,9,7,7,7,7,3,2,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,7,7,7,7,3,3,2,2,1,1,1] .empty .empty))) (.node [12,9,7,7,7,7,4,3,1,1,1,1,1,1] (.node [12,9,7,7,7,7,4,2,2,1,1,1,1,1] (.node [12,9,7,7,7,7,3,3,3,2,1,1] (.node [12,9,7,7,7,7,3,3,3,1,1,1,1] .empty .empty) .empty) (.node [12,9,7,7,7,7,4,2,2,2,2,1] (.node [12,9,7,7,7,7,4,2,2,2,1,1,1] .empty .empty) .empty)) (.node [12,9,7,7,7,7,4,3,3,1,1,1] (.node [12,9,7,7,7,7,4,3,2,2,1,1] (.node [12,9,7,7,7,7,4,3,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,7,7,7,7,4,4,1,1,1,1,1] .empty .empty))))

def degreeTree62_415 : RowTree := (.node [12,9,7,7,7,6,6,2,2,1,1,1,1] degreeTree62_413 degreeTree62_414)

def degreeTree62_416 : RowTree := (.node [12,9,8,5,5,5,5,4,3,2,2,1,1] (.node [12,9,7,7,7,7,6,1,1,1,1,1,1,1] (.node [12,9,7,7,7,7,5,2,2,2,1,1] (.node [12,9,7,7,7,7,5,2,2,1,1,1,1] (.node [12,9,7,7,7,7,5,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,7,7,7,7,5,3,2,1,1,1] (.node [12,9,7,7,7,7,5,3,1,1,1,1,1] .empty .empty) .empty)) (.node [12,9,7,7,7,7,7,1,1,1,1,1,1] (.node [12,9,7,7,7,7,6,2,2,1,1,1] (.node [12,9,7,7,7,7,6,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,5,5,5,4,4,4,2,2,1,1] .empty .empty))) (.node [12,9,8,5,5,5,5,5,4,1,1,1,1] (.node [12,9,8,5,5,5,5,5,2,2,2,1,1] (.node [12,9,8,5,5,5,5,4,4,2,2,1] (.node [12,9,8,5,5,5,5,4,4,2,1,1,1] .empty .empty) .empty) (.node [12,9,8,5,5,5,5,5,3,2,2,1] (.node [12,9,8,5,5,5,5,5,3,2,1,1,1] .empty .empty) .empty)) (.node [12,9,8,6,5,4,4,4,4,2,2,1,1] (.node [12,9,8,5,5,5,5,5,5,1,1,1] (.node [12,9,8,5,5,5,5,5,4,2,1,1] .empty .empty) .empty) (.node [12,9,8,6,5,5,4,4,3,2,2,1,1] .empty .empty))))

def degreeTree62_417 : RowTree := (.node [12,9,8,6,5,5,5,5,3,1,1,1,1] (.node [12,9,8,6,5,5,5,4,3,2,2,1] (.node [12,9,8,6,5,5,5,3,3,2,2,1,1] (.node [12,9,8,6,5,5,5,2,2,2,2,2,2] (.node [12,9,8,6,5,5,4,4,4,2,2,1] .empty .empty) .empty) (.node [12,9,8,6,5,5,5,4,3,2,1,1,1] (.node [12,9,8,6,5,5,5,4,2,2,2,1,1] .empty .empty) .empty)) (.node [12,9,8,6,5,5,5,5,2,2,1,1,1] (.node [12,9,8,6,5,5,5,4,4,2,1,1] (.node [12,9,8,6,5,5,5,4,4,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,6,5,5,5,5,2,2,2,1] .empty .empty))) (.node [12,9,8,6,6,5,4,2,2,2,2,2,2] (.node [12,9,8,6,6,4,4,4,3,2,2,1,1] (.node [12,9,8,6,5,5,5,5,4,1,1,1] (.node [12,9,8,6,5,5,5,5,3,2,1,1] .empty .empty) .empty) (.node [12,9,8,6,6,4,4,4,4,2,2,1] (.node [12,9,8,6,6,4,4,4,4,2,1,1,1] .empty .empty) .empty)) (.node [12,9,8,6,6,5,4,4,3,2,1,1,1] (.node [12,9,8,6,6,5,4,4,2,2,2,1,1] (.node [12,9,8,6,6,5,4,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,8,6,6,5,4,4,3,2,2,1] .empty .empty))))

def degreeTree62_418 : RowTree := (.node [12,9,8,6,5,5,4,4,4,2,1,1,1] degreeTree62_416 degreeTree62_417)

def degreeTree62_419 : RowTree := (.node [12,9,7,7,7,7,4,4,2,1,1,1] degreeTree62_415 degreeTree62_418)

def degreeTree62_420 : RowTree := (.node [12,9,8,6,6,5,5,5,2,1,1,1,1] (.node [12,9,8,6,6,5,5,4,2,2,1,1,1] (.node [12,9,8,6,6,5,5,3,2,2,2,1,1] (.node [12,9,8,6,6,5,5,2,2,2,2,2,1] (.node [12,9,8,6,6,5,4,4,4,2,1,1] .empty .empty) .empty) (.node [12,9,8,6,6,5,5,3,3,2,2,1] (.node [12,9,8,6,6,5,5,3,3,2,1,1,1] .empty .empty) .empty)) (.node [12,9,8,6,6,5,5,4,3,2,1,1] (.node [12,9,8,6,6,5,5,4,3,1,1,1,1] (.node [12,9,8,6,6,5,5,4,2,2,2,1] .empty .empty) .empty) (.node [12,9,8,6,6,5,5,4,4,1,1,1] .empty .empty))) (.node [12,9,8,6,6,6,4,3,2,2,2,1,1] (.node [12,9,8,6,6,6,3,2,2,2,2,2,2] (.node [12,9,8,6,6,5,5,5,3,1,1,1] (.node [12,9,8,6,6,5,5,5,2,2,1,1] .empty .empty) .empty) (.node [12,9,8,6,6,6,4,2,2,2,2,2,1] (.node [12,9,8,6,6,6,3,3,3,2,2,1,1] .empty .empty) .empty)) (.node [12,9,8,6,6,6,4,4,2,2,1,1,1] (.node [12,9,8,6,6,6,4,3,3,2,2,1] (.node [12,9,8,6,6,6,4,3,3,2,1,1,1] .empty .empty) .empty) (.node [12,9,8,6,6,6,4,4,2,2,2,1] .empty .empty))))

def degreeTree62_421 : RowTree := (.node [12,9,8,6,6,6,5,4,3,1,1,1] (.node [12,9,8,6,6,6,5,3,2,2,2,1] (.node [12,9,8,6,6,6,5,2,2,2,2,1,1] (.node [12,9,8,6,6,6,4,4,4,1,1,1] (.node [12,9,8,6,6,6,4,4,3,2,1,1] .empty .empty) .empty) (.node [12,9,8,6,6,6,5,3,2,2,1,1,1] (.node [12,9,8,6,6,6,5,2,2,2,2,2] .empty .empty) .empty)) (.node [12,9,8,6,6,6,5,4,2,1,1,1,1] (.node [12,9,8,6,6,6,5,3,3,2,1,1] (.node [12,9,8,6,6,6,5,3,3,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,6,6,6,5,4,2,2,1,1] .empty .empty))) (.node [12,9,8,6,6,6,6,3,2,2,1,1] (.node [12,9,8,6,6,6,6,2,2,2,1,1,1] (.node [12,9,8,6,6,6,5,5,2,1,1,1] (.node [12,9,8,6,6,6,5,5,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,6,6,6,6,3,2,1,1,1,1] (.node [12,9,8,6,6,6,6,2,2,2,2,1] .empty .empty) .empty)) (.node [12,9,8,6,6,6,6,4,2,1,1,1] (.node [12,9,8,6,6,6,6,4,1,1,1,1,1] (.node [12,9,8,6,6,6,6,3,3,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,4,4,4,4,4,2,2,1,1] .empty .empty))))

def degreeTree62_422 : RowTree := (.node [12,9,8,6,6,6,4,4,3,1,1,1,1] degreeTree62_420 degreeTree62_421)

def degreeTree62_423 : RowTree := (.node [12,9,8,7,5,5,5,3,2,2,2,1,1] (.node [12,9,8,7,5,5,4,4,3,2,1,1,1] (.node [12,9,8,7,5,5,4,2,2,2,2,2,2] (.node [12,9,8,7,5,4,4,4,4,2,2,1] (.node [12,9,8,7,5,4,4,4,4,2,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,5,5,4,4,2,2,2,1,1] (.node [12,9,8,7,5,5,4,3,3,2,2,1,1] .empty .empty) .empty)) (.node [12,9,8,7,5,5,4,4,4,2,1,1] (.node [12,9,8,7,5,5,4,4,4,1,1,1,1] (.node [12,9,8,7,5,5,4,4,3,2,2,1] .empty .empty) .empty) (.node [12,9,8,7,5,5,5,2,2,2,2,2,1] .empty .empty))) (.node [12,9,8,7,5,5,5,4,3,2,1,1] (.node [12,9,8,7,5,5,5,4,2,2,1,1,1] (.node [12,9,8,7,5,5,5,3,3,2,2,1] (.node [12,9,8,7,5,5,5,3,3,2,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,5,5,5,4,3,1,1,1,1] (.node [12,9,8,7,5,5,5,4,2,2,2,1] .empty .empty) .empty)) (.node [12,9,8,7,5,5,5,5,2,2,1,1] (.node [12,9,8,7,5,5,5,5,2,1,1,1,1] (.node [12,9,8,7,5,5,5,4,4,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,5,5,5,5,3,1,1,1] .empty .empty))))

def degreeTree62_424 : RowTree := (.node [12,9,8,7,6,5,4,3,3,2,1,1,1] (.node [12,9,8,7,6,4,4,4,4,2,1,1] (.node [12,9,8,7,6,4,4,4,3,2,1,1,1] (.node [12,9,8,7,6,4,4,4,2,2,2,1,1] (.node [12,9,8,7,6,4,4,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,8,7,6,4,4,4,4,1,1,1,1] (.node [12,9,8,7,6,4,4,4,3,2,2,1] .empty .empty) .empty)) (.node [12,9,8,7,6,5,4,2,2,2,2,2,1] (.node [12,9,8,7,6,5,3,3,3,2,2,1,1] (.node [12,9,8,7,6,5,3,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,9,8,7,6,5,4,3,2,2,2,1,1] .empty .empty))) (.node [12,9,8,7,6,5,4,4,4,1,1,1] (.node [12,9,8,7,6,5,4,4,2,2,2,1] (.node [12,9,8,7,6,5,4,4,2,2,1,1,1] (.node [12,9,8,7,6,5,4,3,3,2,2,1] .empty .empty) .empty) (.node [12,9,8,7,6,5,4,4,3,2,1,1] (.node [12,9,8,7,6,5,4,4,3,1,1,1,1] .empty .empty) .empty)) (.node [12,9,8,7,6,5,5,3,2,2,1,1,1] (.node [12,9,8,7,6,5,5,2,2,2,2,2] (.node [12,9,8,7,6,5,5,2,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,8,7,6,5,5,3,2,2,2,1] .empty .empty))))

def degreeTree62_425 : RowTree := (.node [12,9,8,7,6,4,4,2,2,2,2,2,2] degreeTree62_423 degreeTree62_424)

def degreeTree62_426 : RowTree := (.node [12,9,8,7,5,4,4,4,3,2,2,1,1] degreeTree62_422 degreeTree62_425)

def degreeTree62_427 : RowTree := (.node [12,9,8,6,6,5,4,4,4,1,1,1,1] degreeTree62_419 degreeTree62_426)

def degreeTree62_428 : RowTree := (.node [12,9,8,7,6,6,3,3,3,2,2,1] (.node [12,9,8,7,6,5,5,5,2,1,1,1] (.node [12,9,8,7,6,5,5,4,2,2,1,1] (.node [12,9,8,7,6,5,5,4,2,1,1,1,1] (.node [12,9,8,7,6,5,5,3,3,2,1,1] .empty .empty) .empty) (.node [12,9,8,7,6,5,5,5,1,1,1,1,1] (.node [12,9,8,7,6,5,5,4,3,1,1,1] .empty .empty) .empty)) (.node [12,9,8,7,6,6,3,3,2,2,2,1,1] (.node [12,9,8,7,6,6,3,2,2,2,2,2,1] (.node [12,9,8,7,6,6,2,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,9,8,7,6,6,3,3,3,2,1,1,1] .empty .empty))) (.node [12,9,8,7,6,6,4,3,3,2,1,1] (.node [12,9,8,7,6,6,4,3,2,2,1,1,1] (.node [12,9,8,7,6,6,4,2,2,2,2,2] (.node [12,9,8,7,6,6,4,2,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,8,7,6,6,4,3,3,1,1,1,1] (.node [12,9,8,7,6,6,4,3,2,2,2,1] .empty .empty) .empty)) (.node [12,9,8,7,6,6,4,4,3,1,1,1] (.node [12,9,8,7,6,6,4,4,2,2,1,1] (.node [12,9,8,7,6,6,4,4,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,6,6,5,2,2,2,1,1,1] .empty .empty))))

def degreeTree62_429 : RowTree := (.node [12,9,8,7,7,4,3,2,2,2,2,2,2] (.node [12,9,8,7,6,6,6,2,1,1,1,1,1,1] (.node [12,9,8,7,6,6,5,3,3,1,1,1] (.node [12,9,8,7,6,6,5,3,2,2,1,1] (.node [12,9,8,7,6,6,5,3,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,6,6,5,4,2,1,1,1] (.node [12,9,8,7,6,6,5,4,1,1,1,1,1] .empty .empty) .empty)) (.node [12,9,8,7,6,6,6,3,1,1,1,1,1] (.node [12,9,8,7,6,6,6,2,2,2,1,1] (.node [12,9,8,7,6,6,6,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,6,6,6,3,2,1,1,1] .empty .empty))) (.node [12,9,8,7,7,4,4,4,2,2,1,1,1] (.node [12,9,8,7,7,4,4,3,2,2,2,1,1] (.node [12,9,8,7,7,4,4,2,2,2,2,2,1] (.node [12,9,8,7,7,4,3,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,8,7,7,4,4,3,3,2,2,1] (.node [12,9,8,7,7,4,4,3,3,2,1,1,1] .empty .empty) .empty)) (.node [12,9,8,7,7,4,4,4,3,2,1,1] (.node [12,9,8,7,7,4,4,4,3,1,1,1,1] (.node [12,9,8,7,7,4,4,4,2,2,2,1] .empty .empty) .empty) (.node [12,9,8,7,7,4,4,4,4,1,1,1] .empty .empty))))

def degreeTree62_430 : RowTree := (.node [12,9,8,7,6,6,5,2,2,2,2,1] degreeTree62_428 degreeTree62_429)

def degreeTree62_431 : RowTree := (.node [12,9,8,7,7,5,4,4,2,1,1,1,1] (.node [12,9,8,7,7,5,4,2,2,2,2,2] (.node [12,9,8,7,7,5,3,3,3,2,1,1,1] (.node [12,9,8,7,7,5,3,3,2,2,2,1,1] (.node [12,9,8,7,7,5,3,2,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,8,7,7,5,4,2,2,2,2,1,1] (.node [12,9,8,7,7,5,3,3,3,2,2,1] .empty .empty) .empty)) (.node [12,9,8,7,7,5,4,3,3,1,1,1,1] (.node [12,9,8,7,7,5,4,3,2,2,2,1] (.node [12,9,8,7,7,5,4,3,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,7,5,4,3,3,2,1,1] .empty .empty))) (.node [12,9,8,7,7,5,5,3,2,2,1,1] (.node [12,9,8,7,7,5,5,2,2,2,1,1,1] (.node [12,9,8,7,7,5,4,4,3,1,1,1] (.node [12,9,8,7,7,5,4,4,2,2,1,1] .empty .empty) .empty) (.node [12,9,8,7,7,5,5,3,2,1,1,1,1] (.node [12,9,8,7,7,5,5,2,2,2,2,1] .empty .empty) .empty)) (.node [12,9,8,7,7,5,5,4,2,1,1,1] (.node [12,9,8,7,7,5,5,4,1,1,1,1,1] (.node [12,9,8,7,7,5,5,3,3,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,7,6,2,2,2,2,2,1,1,1] .empty .empty))))

def degreeTree62_432 : RowTree := (.node [12,9,8,7,7,6,4,2,2,2,2,1] (.node [12,9,8,7,7,6,3,3,2,2,2,1] (.node [12,9,8,7,7,6,3,2,2,2,2,2] (.node [12,9,8,7,7,6,3,2,2,2,2,1,1] (.node [12,9,8,7,7,6,3,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,7,6,3,3,2,2,1,1,1] (.node [12,9,8,7,7,6,3,3,2,1,1,1,1,1] .empty .empty) .empty)) (.node [12,9,8,7,7,6,4,2,2,1,1,1,1,1] (.node [12,9,8,7,7,6,3,3,3,2,1,1] (.node [12,9,8,7,7,6,3,3,3,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,7,6,4,2,2,2,1,1,1] .empty .empty))) (.node [12,9,8,7,7,6,4,4,2,1,1,1] (.node [12,9,8,7,7,6,4,3,2,2,1,1] (.node [12,9,8,7,7,6,4,3,2,1,1,1,1] (.node [12,9,8,7,7,6,4,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,7,6,4,4,1,1,1,1,1] (.node [12,9,8,7,7,6,4,3,3,1,1,1] .empty .empty) .empty)) (.node [12,9,8,7,7,6,5,2,2,2,1,1] (.node [12,9,8,7,7,6,5,2,2,1,1,1,1] (.node [12,9,8,7,7,6,5,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,7,6,5,3,1,1,1,1,1] .empty .empty))))

def degreeTree62_433 : RowTree := (.node [12,9,8,7,7,6,2,2,2,2,2,2,1] degreeTree62_431 degreeTree62_432)

def degreeTree62_434 : RowTree := (.node [12,9,8,7,7,5,2,2,2,2,2,2,2] degreeTree62_430 degreeTree62_433)

def degreeTree62_435 : RowTree := (.node [12,9,8,7,7,7,3,3,2,2,1,1] (.node [12,9,8,7,7,7,3,2,2,1,1,1,1,1] (.node [12,9,8,7,7,7,2,2,2,2,1,1,1,1] (.node [12,9,8,7,7,6,6,2,1,1,1,1,1] (.node [12,9,8,7,7,6,6,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,7,7,2,2,2,2,2,2] (.node [12,9,8,7,7,7,2,2,2,2,2,1,1] .empty .empty) .empty)) (.node [12,9,8,7,7,7,3,3,1,1,1,1,1,1] (.node [12,9,8,7,7,7,3,2,2,2,2,1] (.node [12,9,8,7,7,7,3,2,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,7,7,3,3,2,1,1,1,1] .empty .empty))) (.node [12,9,8,7,7,7,5,1,1,1,1,1,1,1] (.node [12,9,8,7,7,7,4,2,2,1,1,1,1] (.node [12,9,8,7,7,7,4,2,1,1,1,1,1,1] (.node [12,9,8,7,7,7,3,3,3,1,1,1] .empty .empty) .empty) (.node [12,9,8,7,7,7,4,3,1,1,1,1,1] (.node [12,9,8,7,7,7,4,2,2,2,1,1] .empty .empty) .empty)) (.node [12,9,8,8,4,4,4,4,3,2,2,1,1] (.node [12,9,8,7,7,7,6,1,1,1,1,1,1] (.node [12,9,8,7,7,7,5,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,4,4,4,4,4,2,1,1,1] .empty .empty))))

def degreeTree62_436 : RowTree := (.node [12,9,8,8,5,5,4,3,2,2,2,1,1] (.node [12,9,8,8,5,4,4,4,4,1,1,1,1] (.node [12,9,8,8,5,4,4,4,2,2,2,1,1] (.node [12,9,8,8,5,4,4,3,3,2,2,1,1] (.node [12,9,8,8,5,4,4,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,9,8,8,5,4,4,4,3,2,2,1] (.node [12,9,8,8,5,4,4,4,3,2,1,1,1] .empty .empty) .empty)) (.node [12,9,8,8,5,5,3,3,3,2,2,1,1] (.node [12,9,8,8,5,5,3,2,2,2,2,2,2] (.node [12,9,8,8,5,4,4,4,4,2,1,1] .empty .empty) .empty) (.node [12,9,8,8,5,5,4,2,2,2,2,2,1] .empty .empty))) (.node [12,9,8,8,5,5,4,4,3,2,1,1] (.node [12,9,8,8,5,5,4,4,2,2,1,1,1] (.node [12,9,8,8,5,5,4,3,3,2,2,1] (.node [12,9,8,8,5,5,4,3,3,2,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,5,5,4,4,3,1,1,1,1] (.node [12,9,8,8,5,5,4,4,2,2,2,1] .empty .empty) .empty)) (.node [12,9,8,8,5,5,5,2,2,2,2,2] (.node [12,9,8,8,5,5,5,2,2,2,2,1,1] (.node [12,9,8,8,5,5,4,4,4,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,5,5,5,3,2,2,1,1,1] .empty .empty))))

def degreeTree62_437 : RowTree := (.node [12,9,8,8,4,4,4,4,4,2,2,1] degreeTree62_435 degreeTree62_436)

def degreeTree62_438 : RowTree := (.node [12,9,8,8,6,4,4,3,2,2,2,1,1] (.node [12,9,8,8,5,5,5,5,1,1,1,1,1] (.node [12,9,8,8,5,5,5,4,2,1,1,1,1] (.node [12,9,8,8,5,5,5,3,3,2,1,1] (.node [12,9,8,8,5,5,5,3,3,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,5,5,5,4,3,1,1,1] (.node [12,9,8,8,5,5,5,4,2,2,1,1] .empty .empty) .empty)) (.node [12,9,8,8,6,4,3,3,3,2,2,1,1] (.node [12,9,8,8,6,4,3,2,2,2,2,2,2] (.node [12,9,8,8,5,5,5,5,2,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,6,4,4,2,2,2,2,2,1] .empty .empty))) (.node [12,9,8,8,6,4,4,4,3,2,1,1] (.node [12,9,8,8,6,4,4,4,2,2,1,1,1] (.node [12,9,8,8,6,4,4,3,3,2,2,1] (.node [12,9,8,8,6,4,4,3,3,2,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,6,4,4,4,3,1,1,1,1] (.node [12,9,8,8,6,4,4,4,2,2,2,1] .empty .empty) .empty)) (.node [12,9,8,8,6,5,3,2,2,2,2,2,1] (.node [12,9,8,8,6,5,2,2,2,2,2,2,2] (.node [12,9,8,8,6,4,4,4,4,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,6,5,3,3,2,2,2,1,1] .empty .empty))))

def degreeTree62_439 : RowTree := (.node [12,9,8,8,6,5,5,2,2,2,1,1,1] (.node [12,9,8,8,6,5,4,3,3,1,1,1,1] (.node [12,9,8,8,6,5,4,2,2,2,2,2] (.node [12,9,8,8,6,5,4,2,2,2,2,1,1] (.node [12,9,8,8,6,5,3,3,3,2,2,1] .empty .empty) .empty) (.node [12,9,8,8,6,5,4,3,2,2,2,1] (.node [12,9,8,8,6,5,4,3,2,2,1,1,1] .empty .empty) .empty)) (.node [12,9,8,8,6,5,4,4,2,2,1,1] (.node [12,9,8,8,6,5,4,4,2,1,1,1,1] (.node [12,9,8,8,6,5,4,3,3,2,1,1] .empty .empty) .empty) (.node [12,9,8,8,6,5,4,4,3,1,1,1] .empty .empty))) (.node [12,9,8,8,6,5,5,4,1,1,1,1,1] (.node [12,9,8,8,6,5,5,3,2,2,1,1] (.node [12,9,8,8,6,5,5,3,2,1,1,1,1] (.node [12,9,8,8,6,5,5,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,8,8,6,5,5,3,3,1,1,1] .empty .empty)) (.node [12,9,8,8,6,6,2,2,2,2,2,2,1] (.node [12,9,8,8,6,6,2,2,2,2,2,1,1,1] (.node [12,9,8,8,6,5,5,4,2,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,6,6,3,2,2,2,1,1,1,1] .empty .empty))))

def degreeTree62_440 : RowTree := (.node [12,9,8,8,6,5,3,3,3,2,1,1,1] degreeTree62_438 degreeTree62_439)

def degreeTree62_441 : RowTree := (.node [12,9,8,8,5,5,5,3,2,2,2,1] degreeTree62_437 degreeTree62_440)

def degreeTree62_442 : RowTree := (.node [12,9,8,7,7,6,5,3,2,1,1,1] degreeTree62_434 degreeTree62_441)

def degreeTree62_443 : RowTree := (.node [12,9,8,7,6,5,5,3,3,1,1,1,1] degreeTree62_427 degreeTree62_442)

def degreeTree62_444 : RowTree := (.node [12,9,7,7,7,6,2,2,2,2,2,2,2] degreeTree62_412 degreeTree62_443)

def degreeTree62_445 : RowTree := (.node [12,9,8,8,6,6,4,3,2,1,1,1,1] (.node [12,9,8,8,6,6,3,3,3,2,1,1] (.node [12,9,8,8,6,6,3,3,2,2,1,1,1] (.node [12,9,8,8,6,6,3,3,2,1,1,1,1,1] (.node [12,9,8,8,6,6,3,2,2,2,2,2] .empty .empty) .empty) (.node [12,9,8,8,6,6,3,3,3,1,1,1,1] (.node [12,9,8,8,6,6,3,3,2,2,2,1] .empty .empty) .empty)) (.node [12,9,8,8,6,6,4,2,2,2,2,1] (.node [12,9,8,8,6,6,4,2,2,2,1,1,1] (.node [12,9,8,8,6,6,4,2,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,6,6,4,3,1,1,1,1,1,1] .empty .empty))) (.node [12,9,8,8,6,6,5,2,2,1,1,1,1] (.node [12,9,8,8,6,6,4,4,1,1,1,1,1] (.node [12,9,8,8,6,6,4,3,3,1,1,1] (.node [12,9,8,8,6,6,4,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,8,8,6,6,5,2,1,1,1,1,1,1] (.node [12,9,8,8,6,6,4,4,2,1,1,1] .empty .empty) .empty)) (.node [12,9,8,8,6,6,6,1,1,1,1,1,1,1] (.node [12,9,8,8,6,6,5,3,1,1,1,1,1] (.node [12,9,8,8,6,6,5,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,8,8,6,6,6,2,1,1,1,1,1] .empty .empty))))

def degreeTree62_446 : RowTree := (.node [12,9,8,8,7,4,4,2,2,2,2,2] (.node [12,9,8,8,7,4,3,3,3,1,1,1,1,1] (.node [12,9,8,8,7,4,3,2,2,2,2,1,1,1] (.node [12,9,8,8,7,4,2,2,2,2,2,2,2] (.node [12,9,8,8,7,3,3,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,8,8,7,4,3,3,2,2,2,1,1] (.node [12,9,8,8,7,4,3,2,2,2,2,2,1] .empty .empty) .empty)) (.node [12,9,8,8,7,4,4,2,2,2,1,1,1,1] (.node [12,9,8,8,7,4,3,3,3,2,2,1] (.node [12,9,8,8,7,4,3,3,3,2,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,7,4,4,2,2,2,2,1,1] .empty .empty))) (.node [12,9,8,8,7,4,4,4,1,1,1,1,1,1] (.node [12,9,8,8,7,4,4,3,2,2,2,1] (.node [12,9,8,8,7,4,4,3,2,2,1,1,1] (.node [12,9,8,8,7,4,4,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,7,4,4,3,3,2,1,1] (.node [12,9,8,8,7,4,4,3,3,1,1,1,1] .empty .empty) .empty)) (.node [12,9,8,8,7,4,4,4,3,1,1,1] (.node [12,9,8,8,7,4,4,4,2,2,1,1] (.node [12,9,8,8,7,4,4,4,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,7,5,2,2,2,2,2,1,1,1] .empty .empty))))

def degreeTree62_447 : RowTree := (.node [12,9,8,8,7,3,3,2,2,2,2,2,2] degreeTree62_445 degreeTree62_446)

def degreeTree62_448 : RowTree := (.node [12,9,8,8,7,5,4,2,2,2,2,1] (.node [12,9,8,8,7,5,3,3,2,2,2,1] (.node [12,9,8,8,7,5,3,2,2,2,2,2] (.node [12,9,8,8,7,5,3,2,2,2,2,1,1] (.node [12,9,8,8,7,5,3,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,7,5,3,3,2,2,1,1,1] (.node [12,9,8,8,7,5,3,3,2,1,1,1,1,1] .empty .empty) .empty)) (.node [12,9,8,8,7,5,4,2,2,1,1,1,1,1] (.node [12,9,8,8,7,5,3,3,3,2,1,1] (.node [12,9,8,8,7,5,3,3,3,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,7,5,4,2,2,2,1,1,1] .empty .empty))) (.node [12,9,8,8,7,5,5,2,1,1,1,1,1,1] (.node [12,9,8,8,7,5,4,3,2,2,1,1] (.node [12,9,8,8,7,5,4,3,2,1,1,1,1] (.node [12,9,8,8,7,5,4,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,7,5,4,4,1,1,1,1,1] (.node [12,9,8,8,7,5,4,3,3,1,1,1] .empty .empty) .empty)) (.node [12,9,8,8,7,5,5,3,1,1,1,1,1] (.node [12,9,8,8,7,5,5,2,2,2,1,1] (.node [12,9,8,8,7,5,5,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,7,6,2,2,2,2,1,1,1,1] .empty .empty))))

def degreeTree62_449 : RowTree := (.node [12,9,8,8,7,6,4,2,2,2,1,1] (.node [12,9,8,8,7,6,3,3,2,1,1,1,1] (.node [12,9,8,8,7,6,3,2,2,2,1,1,1] (.node [12,9,8,8,7,6,3,2,2,1,1,1,1,1] (.node [12,9,8,8,7,6,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,9,8,8,7,6,3,3,1,1,1,1,1,1] (.node [12,9,8,8,7,6,3,2,2,2,2,1] .empty .empty) .empty)) (.node [12,9,8,8,7,6,4,2,1,1,1,1,1,1] (.node [12,9,8,8,7,6,3,3,3,1,1,1] (.node [12,9,8,8,7,6,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,8,8,7,6,4,2,2,1,1,1,1] .empty .empty))) (.node [12,9,8,8,7,7,2,2,2,2,1,1,1] (.node [12,9,8,8,7,6,5,2,1,1,1,1,1] (.node [12,9,8,8,7,6,5,1,1,1,1,1,1,1] (.node [12,9,8,8,7,6,4,3,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,7,7,2,2,2,1,1,1,1,1] (.node [12,9,8,8,7,6,6,1,1,1,1,1,1] .empty .empty) .empty)) (.node [12,9,8,8,7,7,3,2,2,1,1,1,1] (.node [12,9,8,8,7,7,3,2,1,1,1,1,1,1] (.node [12,9,8,8,7,7,2,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,8,8,7,7,3,2,2,2,1,1] .empty .empty))))

def degreeTree62_450 : RowTree := (.node [12,9,8,8,7,6,2,2,2,2,2,1,1] degreeTree62_448 degreeTree62_449)

def degreeTree62_451 : RowTree := (.node [12,9,8,8,7,5,2,2,2,2,2,2,1] degreeTree62_447 degreeTree62_450)

def degreeTree62_452 : RowTree := (.node [12,9,8,8,8,3,3,3,3,2,2,1] (.node [12,9,8,8,8,3,3,2,2,2,2,1,1,1] (.node [12,9,8,8,7,7,5,1,1,1,1,1,1] (.node [12,9,8,8,7,7,4,2,1,1,1,1,1] (.node [12,9,8,8,7,7,4,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,8,3,2,2,2,2,2,2,2] (.node [12,9,8,8,8,2,2,2,2,2,2,2,2,1] .empty .empty) .empty)) (.node [12,9,8,8,8,3,3,3,3,1,1,1,1,1] (.node [12,9,8,8,8,3,3,3,2,2,2,1,1] (.node [12,9,8,8,8,3,3,2,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,8,8,8,3,3,3,3,2,1,1,1] .empty .empty))) (.node [12,9,8,8,8,4,3,3,2,1,1,1,1,1] (.node [12,9,8,8,8,4,3,2,2,2,1,1,1,1] (.node [12,9,8,8,8,4,2,2,2,2,2,2,1] (.node [12,9,8,8,8,4,2,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,8,4,3,2,2,2,2,2] (.node [12,9,8,8,8,4,3,2,2,2,2,1,1] .empty .empty) .empty)) (.node [12,9,8,8,8,4,3,3,3,1,1,1,1] (.node [12,9,8,8,8,4,3,3,2,2,2,1] (.node [12,9,8,8,8,4,3,3,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,8,4,3,3,3,2,1,1] .empty .empty))))

def degreeTree62_453 : RowTree := (.node [12,9,8,8,8,5,3,2,2,1,1,1,1,1] (.node [12,9,8,8,8,4,4,3,3,1,1,1] (.node [12,9,8,8,8,4,4,3,1,1,1,1,1,1] (.node [12,9,8,8,8,4,4,2,2,2,2,1] (.node [12,9,8,8,8,4,4,2,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,8,4,4,3,2,2,1,1] (.node [12,9,8,8,8,4,4,3,2,1,1,1,1] .empty .empty) .empty)) (.node [12,9,8,8,8,5,2,2,2,2,2,1,1] (.node [12,9,8,8,8,5,2,2,2,2,1,1,1,1] (.node [12,9,8,8,8,4,4,4,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,8,5,2,2,2,2,2,2] .empty .empty))) (.node [12,9,8,8,8,5,3,3,3,1,1,1] (.node [12,9,8,8,8,5,3,3,1,1,1,1,1,1] (.node [12,9,8,8,8,5,3,2,2,2,2,1] (.node [12,9,8,8,8,5,3,2,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,8,5,3,3,2,2,1,1] (.node [12,9,8,8,8,5,3,3,2,1,1,1,1] .empty .empty) .empty)) (.node [12,9,8,8,8,5,4,2,2,2,1,1] (.node [12,9,8,8,8,5,4,2,2,1,1,1,1] (.node [12,9,8,8,8,5,4,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,8,5,4,3,1,1,1,1,1] .empty .empty))))

def degreeTree62_454 : RowTree := (.node [12,9,8,8,8,4,4,2,2,1,1,1,1,1] degreeTree62_452 degreeTree62_453)

def degreeTree62_455 : RowTree := (.node [12,9,8,8,8,6,5,1,1,1,1,1,1] (.node [12,9,8,8,8,6,3,2,2,1,1,1,1] (.node [12,9,8,8,8,6,2,2,2,2,1,1,1] (.node [12,9,8,8,8,6,2,2,2,1,1,1,1,1] (.node [12,9,8,8,8,5,5,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,8,6,3,2,1,1,1,1,1,1] (.node [12,9,8,8,8,6,2,2,2,2,2,1] .empty .empty) .empty)) (.node [12,9,8,8,8,6,4,1,1,1,1,1,1,1] (.node [12,9,8,8,8,6,3,3,1,1,1,1,1] (.node [12,9,8,8,8,6,3,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,8,8,8,6,4,2,1,1,1,1,1] .empty .empty))) (.node [12,9,8,8,8,7,4,1,1,1,1,1,1] (.node [12,9,8,8,8,7,2,2,2,2,1,1] (.node [12,9,8,8,8,7,2,2,2,1,1,1,1] (.node [12,9,8,8,8,7,2,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,8,8,8,7,3,2,1,1,1,1,1] (.node [12,9,8,8,8,7,3,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [12,9,8,8,8,8,3,1,1,1,1,1,1] (.node [12,9,8,8,8,8,2,2,1,1,1,1,1] (.node [12,9,8,8,8,8,2,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,5,5,4,4,4,4,2,2,1,1] .empty .empty))))

def degreeTree62_456 : RowTree := (.node [12,9,9,5,5,5,5,5,2,2,2,1] (.node [12,9,9,5,5,5,5,4,3,2,1,1,1] (.node [12,9,9,5,5,5,5,2,2,2,2,2,2] (.node [12,9,9,5,5,5,4,4,4,2,2,1] (.node [12,9,9,5,5,5,4,4,4,2,1,1,1] .empty .empty) .empty) (.node [12,9,9,5,5,5,5,4,2,2,2,1,1] (.node [12,9,9,5,5,5,5,3,3,2,2,1,1] .empty .empty) .empty)) (.node [12,9,9,5,5,5,5,4,4,2,1,1] (.node [12,9,9,5,5,5,5,4,4,1,1,1,1] (.node [12,9,9,5,5,5,5,4,3,2,2,1] .empty .empty) .empty) (.node [12,9,9,5,5,5,5,5,2,2,1,1,1] .empty .empty))) (.node [12,9,9,6,5,4,4,4,4,2,1,1,1] (.node [12,9,9,5,5,5,5,5,4,1,1,1] (.node [12,9,9,5,5,5,5,5,3,2,1,1] (.node [12,9,9,5,5,5,5,5,3,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,6,5,4,4,4,3,2,2,1,1] (.node [12,9,9,6,4,4,4,4,4,2,2,1,1] .empty .empty) .empty)) (.node [12,9,9,6,5,5,4,3,3,2,2,1,1] (.node [12,9,9,6,5,5,4,2,2,2,2,2,2] (.node [12,9,9,6,5,4,4,4,4,2,2,1] .empty .empty) .empty) (.node [12,9,9,6,5,5,4,4,2,2,2,1,1] .empty .empty))))

def degreeTree62_457 : RowTree := (.node [12,9,9,5,5,5,4,4,3,2,2,1,1] degreeTree62_455 degreeTree62_456)

def degreeTree62_458 : RowTree := (.node [12,9,8,8,8,5,5,1,1,1,1,1,1,1] degreeTree62_454 degreeTree62_457)

def degreeTree62_459 : RowTree := (.node [12,9,8,8,7,7,3,3,1,1,1,1,1] degreeTree62_451 degreeTree62_458)

def degreeTree62_460 : RowTree := (.node [12,9,9,6,5,5,5,4,3,2,1,1] (.node [12,9,9,6,5,5,5,3,3,2,1,1,1] (.node [12,9,9,6,5,5,4,4,4,2,1,1] (.node [12,9,9,6,5,5,4,4,4,1,1,1,1] (.node [12,9,9,6,5,5,4,4,3,2,2,1] .empty .empty) .empty) (.node [12,9,9,6,5,5,5,3,2,2,2,1,1] (.node [12,9,9,6,5,5,5,2,2,2,2,2,1] .empty .empty) .empty)) (.node [12,9,9,6,5,5,5,4,2,2,2,1] (.node [12,9,9,6,5,5,5,4,2,2,1,1,1] (.node [12,9,9,6,5,5,5,3,3,2,2,1] .empty .empty) .empty) (.node [12,9,9,6,5,5,5,4,3,1,1,1,1] .empty .empty))) (.node [12,9,9,6,6,4,4,3,3,2,2,1,1] (.node [12,9,9,6,5,5,5,5,2,2,1,1] (.node [12,9,9,6,5,5,5,5,2,1,1,1,1] (.node [12,9,9,6,5,5,5,4,4,1,1,1] .empty .empty) .empty) (.node [12,9,9,6,6,4,4,2,2,2,2,2,2] (.node [12,9,9,6,5,5,5,5,3,1,1,1] .empty .empty) .empty)) (.node [12,9,9,6,6,4,4,4,3,2,2,1] (.node [12,9,9,6,6,4,4,4,3,2,1,1,1] (.node [12,9,9,6,6,4,4,4,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,6,6,4,4,4,4,1,1,1,1] .empty .empty))))

def degreeTree62_461 : RowTree := (.node [12,9,9,6,6,5,4,4,4,1,1,1] (.node [12,9,9,6,6,5,4,3,3,2,2,1] (.node [12,9,9,6,6,5,4,2,2,2,2,2,1] (.node [12,9,9,6,6,5,3,3,3,2,2,1,1] (.node [12,9,9,6,6,5,3,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,9,9,6,6,5,4,3,3,2,1,1,1] (.node [12,9,9,6,6,5,4,3,2,2,2,1,1] .empty .empty) .empty)) (.node [12,9,9,6,6,5,4,4,3,1,1,1,1] (.node [12,9,9,6,6,5,4,4,2,2,2,1] (.node [12,9,9,6,6,5,4,4,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,9,6,6,5,4,4,3,2,1,1] .empty .empty))) (.node [12,9,9,6,6,5,5,3,3,2,1,1] (.node [12,9,9,6,6,5,5,3,2,2,1,1,1] (.node [12,9,9,6,6,5,5,2,2,2,2,2] (.node [12,9,9,6,6,5,5,2,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,6,6,5,5,3,3,1,1,1,1] (.node [12,9,9,6,6,5,5,3,2,2,2,1] .empty .empty) .empty)) (.node [12,9,9,6,6,5,5,4,3,1,1,1] (.node [12,9,9,6,6,5,5,4,2,2,1,1] (.node [12,9,9,6,6,5,5,4,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,6,6,5,5,5,1,1,1,1,1] .empty .empty))))

def degreeTree62_462 : RowTree := (.node [12,9,9,6,6,4,4,4,4,2,1,1] degreeTree62_460 degreeTree62_461)

def degreeTree62_463 : RowTree := (.node [12,9,9,6,6,6,4,4,2,1,1,1,1] (.node [12,9,9,6,6,6,4,2,2,2,2,2] (.node [12,9,9,6,6,6,3,3,3,2,1,1,1] (.node [12,9,9,6,6,6,3,3,2,2,2,1,1] (.node [12,9,9,6,6,6,3,2,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,9,6,6,6,4,2,2,2,2,1,1] (.node [12,9,9,6,6,6,3,3,3,2,2,1] .empty .empty) .empty)) (.node [12,9,9,6,6,6,4,3,3,1,1,1,1] (.node [12,9,9,6,6,6,4,3,2,2,2,1] (.node [12,9,9,6,6,6,4,3,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,9,6,6,6,4,3,3,2,1,1] .empty .empty))) (.node [12,9,9,6,6,6,5,3,2,2,1,1] (.node [12,9,9,6,6,6,5,2,2,2,1,1,1] (.node [12,9,9,6,6,6,4,4,3,1,1,1] (.node [12,9,9,6,6,6,4,4,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,6,6,6,5,3,2,1,1,1,1] (.node [12,9,9,6,6,6,5,2,2,2,2,1] .empty .empty) .empty)) (.node [12,9,9,6,6,6,6,2,1,1,1,1,1,1] (.node [12,9,9,6,6,6,5,4,1,1,1,1,1] (.node [12,9,9,6,6,6,5,3,3,1,1,1] .empty .empty) .empty) (.node [12,9,9,6,6,6,6,2,2,1,1,1,1] .empty .empty))))

def degreeTree62_464 : RowTree := (.node [12,9,9,7,5,4,4,4,4,2,1,1] (.node [12,9,9,7,5,4,4,3,3,2,2,1,1] (.node [12,9,9,7,4,4,4,4,4,2,1,1,1] (.node [12,9,9,7,4,4,4,4,3,2,2,1,1] (.node [12,9,9,6,6,6,6,3,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,7,5,4,4,2,2,2,2,2,2] (.node [12,9,9,7,4,4,4,4,4,2,2,1] .empty .empty) .empty)) (.node [12,9,9,7,5,4,4,4,3,2,2,1] (.node [12,9,9,7,5,4,4,4,3,2,1,1,1] (.node [12,9,9,7,5,4,4,4,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,7,5,4,4,4,4,1,1,1,1] .empty .empty))) (.node [12,9,9,7,5,5,4,3,3,2,2,1] (.node [12,9,9,7,5,5,4,2,2,2,2,2,1] (.node [12,9,9,7,5,5,3,3,3,2,2,1,1] (.node [12,9,9,7,5,5,3,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,9,9,7,5,5,4,3,3,2,1,1,1] (.node [12,9,9,7,5,5,4,3,2,2,2,1,1] .empty .empty) .empty)) (.node [12,9,9,7,5,5,4,4,3,1,1,1,1] (.node [12,9,9,7,5,5,4,4,2,2,2,1] (.node [12,9,9,7,5,5,4,4,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,9,7,5,5,4,4,3,2,1,1] .empty .empty))))

def degreeTree62_465 : RowTree := (.node [12,9,9,6,6,6,6,2,2,2,1,1] degreeTree62_463 degreeTree62_464)

def degreeTree62_466 : RowTree := (.node [12,9,9,6,6,6,2,2,2,2,2,2,2] degreeTree62_462 degreeTree62_465)

def degreeTree62_467 : RowTree := (.node [12,9,9,7,6,4,3,2,2,2,2,2,2] (.node [12,9,9,7,5,5,5,3,3,2,1,1] (.node [12,9,9,7,5,5,5,3,2,2,1,1,1] (.node [12,9,9,7,5,5,5,2,2,2,2,2] (.node [12,9,9,7,5,5,5,2,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,7,5,5,5,3,3,1,1,1,1] (.node [12,9,9,7,5,5,5,3,2,2,2,1] .empty .empty) .empty)) (.node [12,9,9,7,5,5,5,4,3,1,1,1] (.node [12,9,9,7,5,5,5,4,2,2,1,1] (.node [12,9,9,7,5,5,5,4,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,7,5,5,5,5,1,1,1,1,1] .empty .empty))) (.node [12,9,9,7,6,4,4,4,2,2,1,1,1] (.node [12,9,9,7,6,4,4,3,2,2,2,1,1] (.node [12,9,9,7,6,4,4,2,2,2,2,2,1] (.node [12,9,9,7,6,4,3,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,7,6,4,4,3,3,2,2,1] (.node [12,9,9,7,6,4,4,3,3,2,1,1,1] .empty .empty) .empty)) (.node [12,9,9,7,6,4,4,4,3,2,1,1] (.node [12,9,9,7,6,4,4,4,3,1,1,1,1] (.node [12,9,9,7,6,4,4,4,2,2,2,1] .empty .empty) .empty) (.node [12,9,9,7,6,4,4,4,4,1,1,1] .empty .empty))))

def degreeTree62_468 : RowTree := (.node [12,9,9,7,6,5,4,4,2,1,1,1,1] (.node [12,9,9,7,6,5,4,2,2,2,2,2] (.node [12,9,9,7,6,5,3,3,3,2,1,1,1] (.node [12,9,9,7,6,5,3,3,2,2,2,1,1] (.node [12,9,9,7,6,5,3,2,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,9,7,6,5,4,2,2,2,2,1,1] (.node [12,9,9,7,6,5,3,3,3,2,2,1] .empty .empty) .empty)) (.node [12,9,9,7,6,5,4,3,3,1,1,1,1] (.node [12,9,9,7,6,5,4,3,2,2,2,1] (.node [12,9,9,7,6,5,4,3,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,9,7,6,5,4,3,3,2,1,1] .empty .empty))) (.node [12,9,9,7,6,5,5,3,2,2,1,1] (.node [12,9,9,7,6,5,5,2,2,2,1,1,1] (.node [12,9,9,7,6,5,4,4,3,1,1,1] (.node [12,9,9,7,6,5,4,4,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,7,6,5,5,3,2,1,1,1,1] (.node [12,9,9,7,6,5,5,2,2,2,2,1] .empty .empty) .empty)) (.node [12,9,9,7,6,6,2,2,2,2,2,1,1,1] (.node [12,9,9,7,6,5,5,4,1,1,1,1,1] (.node [12,9,9,7,6,5,5,3,3,1,1,1] .empty .empty) .empty) (.node [12,9,9,7,6,6,2,2,2,2,2,2,1] .empty .empty))))

def degreeTree62_469 : RowTree := (.node [12,9,9,7,6,5,2,2,2,2,2,2,2] degreeTree62_467 degreeTree62_468)

def degreeTree62_470 : RowTree := (.node [12,9,9,7,6,6,4,3,1,1,1,1,1,1] (.node [12,9,9,7,6,6,3,3,3,1,1,1,1] (.node [12,9,9,7,6,6,3,3,2,1,1,1,1,1] (.node [12,9,9,7,6,6,3,2,2,2,2,2] (.node [12,9,9,7,6,6,3,2,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,7,6,6,3,3,2,2,2,1] (.node [12,9,9,7,6,6,3,3,2,2,1,1,1] .empty .empty) .empty)) (.node [12,9,9,7,6,6,4,2,2,2,1,1,1] (.node [12,9,9,7,6,6,4,2,2,1,1,1,1,1] (.node [12,9,9,7,6,6,3,3,3,2,1,1] .empty .empty) .empty) (.node [12,9,9,7,6,6,4,2,2,2,2,1] .empty .empty))) (.node [12,9,9,7,6,6,5,2,2,1,1,1,1] (.node [12,9,9,7,6,6,4,3,3,1,1,1] (.node [12,9,9,7,6,6,4,3,2,2,1,1] (.node [12,9,9,7,6,6,4,3,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,7,6,6,5,2,1,1,1,1,1,1] (.node [12,9,9,7,6,6,4,4,1,1,1,1,1] .empty .empty) .empty)) (.node [12,9,9,7,6,6,6,1,1,1,1,1,1,1] (.node [12,9,9,7,6,6,5,3,1,1,1,1,1] (.node [12,9,9,7,6,6,5,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,7,6,6,6,2,1,1,1,1,1] .empty .empty))))

def degreeTree62_471 : RowTree := (.node [12,9,9,7,7,4,4,2,2,2,2,2] (.node [12,9,9,7,7,4,3,3,3,1,1,1,1,1] (.node [12,9,9,7,7,4,3,2,2,2,2,1,1,1] (.node [12,9,9,7,7,4,2,2,2,2,2,2,2] (.node [12,9,9,7,7,3,3,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,7,7,4,3,3,2,2,2,1,1] (.node [12,9,9,7,7,4,3,2,2,2,2,2,1] .empty .empty) .empty)) (.node [12,9,9,7,7,4,4,2,2,2,1,1,1,1] (.node [12,9,9,7,7,4,3,3,3,2,2,1] (.node [12,9,9,7,7,4,3,3,3,2,1,1,1] .empty .empty) .empty) (.node [12,9,9,7,7,4,4,2,2,2,2,1,1] .empty .empty))) (.node [12,9,9,7,7,4,4,3,3,2,1,1] (.node [12,9,9,7,7,4,4,3,2,2,2,1] (.node [12,9,9,7,7,4,4,3,2,2,1,1,1] (.node [12,9,9,7,7,4,4,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,7,7,4,4,3,3,1,1,1,1] .empty .empty)) (.node [12,9,9,7,7,4,4,4,2,2,1,1] (.node [12,9,9,7,7,4,4,4,2,1,1,1,1] (.node [12,9,9,7,7,4,4,4,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,7,7,4,4,4,3,1,1,1] .empty .empty))))

def degreeTree62_472 : RowTree := (.node [12,9,9,7,7,3,3,2,2,2,2,2,2] degreeTree62_470 degreeTree62_471)

def degreeTree62_473 : RowTree := (.node [12,9,9,7,6,6,3,2,2,2,1,1,1,1] degreeTree62_469 degreeTree62_472)

def degreeTree62_474 : RowTree := (.node [12,9,9,7,5,5,4,4,4,1,1,1] degreeTree62_466 degreeTree62_473)

def degreeTree62_475 : RowTree := (.node [12,9,9,6,5,5,4,4,3,2,1,1,1] degreeTree62_459 degreeTree62_474)

def degreeTree62_476 : RowTree := (.node [12,9,9,7,7,5,4,2,2,2,1,1,1] (.node [12,9,9,7,7,5,3,3,2,2,1,1,1] (.node [12,9,9,7,7,5,3,2,2,2,2,1,1] (.node [12,9,9,7,7,5,3,2,2,2,1,1,1,1] (.node [12,9,9,7,7,5,2,2,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,9,7,7,5,3,3,2,1,1,1,1,1] (.node [12,9,9,7,7,5,3,2,2,2,2,2] .empty .empty) .empty)) (.node [12,9,9,7,7,5,3,3,3,2,1,1] (.node [12,9,9,7,7,5,3,3,3,1,1,1,1] (.node [12,9,9,7,7,5,3,3,2,2,2,1] .empty .empty) .empty) (.node [12,9,9,7,7,5,4,2,2,1,1,1,1,1] .empty .empty))) (.node [12,9,9,7,7,5,5,2,1,1,1,1,1,1] (.node [12,9,9,7,7,5,4,3,2,1,1,1,1] (.node [12,9,9,7,7,5,4,3,1,1,1,1,1,1] (.node [12,9,9,7,7,5,4,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,9,7,7,5,4,4,1,1,1,1,1] (.node [12,9,9,7,7,5,4,3,2,2,1,1] .empty .empty) .empty)) (.node [12,9,9,7,7,5,5,3,1,1,1,1,1] (.node [12,9,9,7,7,5,5,2,2,2,1,1] (.node [12,9,9,7,7,5,5,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,7,7,6,2,2,2,2,1,1,1,1] .empty .empty))))

def degreeTree62_477 : RowTree := (.node [12,9,9,7,7,6,4,3,1,1,1,1,1] (.node [12,9,9,7,7,6,3,3,2,1,1,1,1] (.node [12,9,9,7,7,6,3,2,2,2,1,1,1] (.node [12,9,9,7,7,6,3,2,2,1,1,1,1,1] (.node [12,9,9,7,7,6,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,9,9,7,7,6,3,3,1,1,1,1,1,1] (.node [12,9,9,7,7,6,3,2,2,2,2,1] .empty .empty) .empty)) (.node [12,9,9,7,7,6,4,2,2,1,1,1,1] (.node [12,9,9,7,7,6,4,2,1,1,1,1,1,1] (.node [12,9,9,7,7,6,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,7,7,6,4,2,2,2,1,1] .empty .empty))) (.node [12,9,9,7,7,7,2,2,2,2,2,1] (.node [12,9,9,7,7,6,6,1,1,1,1,1,1] (.node [12,9,9,7,7,6,5,2,1,1,1,1,1] (.node [12,9,9,7,7,6,5,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,7,7,7,2,2,2,2,1,1,1] (.node [12,9,9,7,7,7,2,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [12,9,9,7,7,7,3,2,2,2,1,1] (.node [12,9,9,7,7,7,3,2,2,1,1,1,1] (.node [12,9,9,7,7,7,3,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,7,7,7,3,3,1,1,1,1,1] .empty .empty))))

def degreeTree62_478 : RowTree := (.node [12,9,9,7,7,6,2,2,2,2,2,1,1] degreeTree62_476 degreeTree62_477)

def degreeTree62_479 : RowTree := (.node [12,9,9,8,5,4,3,3,3,2,2,1,1] (.node [12,9,9,8,4,4,4,4,3,2,1,1,1] (.node [12,9,9,8,4,4,4,2,2,2,2,2,2] (.node [12,9,9,7,7,7,5,1,1,1,1,1,1] (.node [12,9,9,7,7,7,4,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,4,4,4,4,2,2,2,1,1] (.node [12,9,9,8,4,4,4,3,3,2,2,1,1] .empty .empty) .empty)) (.node [12,9,9,8,4,4,4,4,4,2,1,1] (.node [12,9,9,8,4,4,4,4,4,1,1,1,1] (.node [12,9,9,8,4,4,4,4,3,2,2,1] .empty .empty) .empty) (.node [12,9,9,8,5,4,3,2,2,2,2,2,2] .empty .empty))) (.node [12,9,9,8,5,4,4,4,2,2,2,1] (.node [12,9,9,8,5,4,4,3,3,2,1,1,1] (.node [12,9,9,8,5,4,4,3,2,2,2,1,1] (.node [12,9,9,8,5,4,4,2,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,9,8,5,4,4,4,2,2,1,1,1] (.node [12,9,9,8,5,4,4,3,3,2,2,1] .empty .empty) .empty)) (.node [12,9,9,8,5,4,4,4,4,1,1,1] (.node [12,9,9,8,5,4,4,4,3,2,1,1] (.node [12,9,9,8,5,4,4,4,3,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,5,5,2,2,2,2,2,2,2] .empty .empty))))

def degreeTree62_480 : RowTree := (.node [12,9,9,8,5,5,4,4,2,2,1,1] (.node [12,9,9,8,5,5,4,3,2,2,1,1,1] (.node [12,9,9,8,5,5,3,3,3,2,2,1] (.node [12,9,9,8,5,5,3,3,3,2,1,1,1] (.node [12,9,9,8,5,5,3,3,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,8,5,5,4,2,2,2,2,2] (.node [12,9,9,8,5,5,4,2,2,2,2,1,1] .empty .empty) .empty)) (.node [12,9,9,8,5,5,4,3,3,2,1,1] (.node [12,9,9,8,5,5,4,3,3,1,1,1,1] (.node [12,9,9,8,5,5,4,3,2,2,2,1] .empty .empty) .empty) (.node [12,9,9,8,5,5,4,4,2,1,1,1,1] .empty .empty))) (.node [12,9,9,8,5,5,5,4,1,1,1,1,1] (.node [12,9,9,8,5,5,5,2,2,2,2,1] (.node [12,9,9,8,5,5,5,2,2,2,1,1,1] (.node [12,9,9,8,5,5,4,4,3,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,5,5,5,3,2,2,1,1] (.node [12,9,9,8,5,5,5,3,2,1,1,1,1] .empty .empty) .empty)) (.node [12,9,9,8,6,4,2,2,2,2,2,2,2] (.node [12,9,9,8,6,3,3,3,3,2,2,1,1] (.node [12,9,9,8,6,3,3,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,9,9,8,6,4,3,2,2,2,2,1,1,1] .empty .empty))))

def degreeTree62_481 : RowTree := (.node [12,9,9,8,5,5,3,2,2,2,2,2,1] degreeTree62_479 degreeTree62_480)

def degreeTree62_482 : RowTree := (.node [12,9,9,7,7,7,4,1,1,1,1,1,1,1] degreeTree62_478 degreeTree62_481)

def degreeTree62_483 : RowTree := (.node [12,9,9,8,6,4,4,3,3,1,1,1,1] (.node [12,9,9,8,6,4,4,2,2,2,2,1,1] (.node [12,9,9,8,6,4,3,3,3,2,1,1,1] (.node [12,9,9,8,6,4,3,3,3,1,1,1,1,1] (.node [12,9,9,8,6,4,3,3,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,8,6,4,4,2,2,2,1,1,1,1] (.node [12,9,9,8,6,4,3,3,3,2,2,1] .empty .empty) .empty)) (.node [12,9,9,8,6,4,4,3,2,2,1,1,1] (.node [12,9,9,8,6,4,4,3,2,1,1,1,1,1] (.node [12,9,9,8,6,4,4,2,2,2,2,2] .empty .empty) .empty) (.node [12,9,9,8,6,4,4,3,2,2,2,1] .empty .empty))) (.node [12,9,9,8,6,5,2,2,2,2,2,2,1] (.node [12,9,9,8,6,4,4,4,2,1,1,1,1] (.node [12,9,9,8,6,4,4,4,1,1,1,1,1,1] (.node [12,9,9,8,6,4,4,3,3,2,1,1] .empty .empty) .empty) (.node [12,9,9,8,6,5,2,2,2,2,2,1,1,1] (.node [12,9,9,8,6,4,4,4,2,2,1,1] .empty .empty) .empty)) (.node [12,9,9,8,6,5,3,2,2,2,2,2] (.node [12,9,9,8,6,5,3,2,2,2,2,1,1] (.node [12,9,9,8,6,5,3,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,6,5,3,3,2,1,1,1,1,1] .empty .empty))))

def degreeTree62_484 : RowTree := (.node [12,9,9,8,6,5,5,2,1,1,1,1,1,1] (.node [12,9,9,8,6,5,4,2,2,2,2,1] (.node [12,9,9,8,6,5,3,3,3,2,1,1] (.node [12,9,9,8,6,5,3,3,3,1,1,1,1] (.node [12,9,9,8,6,5,3,3,2,2,2,1] .empty .empty) .empty) (.node [12,9,9,8,6,5,4,2,2,2,1,1,1] (.node [12,9,9,8,6,5,4,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [12,9,9,8,6,5,4,3,2,2,1,1] (.node [12,9,9,8,6,5,4,3,2,1,1,1,1] (.node [12,9,9,8,6,5,4,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,6,5,4,4,1,1,1,1,1] .empty .empty))) (.node [12,9,9,8,6,6,2,2,2,2,2,2] (.node [12,9,9,8,6,5,5,3,1,1,1,1,1] (.node [12,9,9,8,6,5,5,2,2,2,1,1] (.node [12,9,9,8,6,5,5,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,6,6,2,2,2,2,2,1,1] (.node [12,9,9,8,6,6,2,2,2,2,1,1,1,1] .empty .empty) .empty)) (.node [12,9,9,8,6,6,3,2,2,2,2,1] (.node [12,9,9,8,6,6,3,2,2,2,1,1,1] (.node [12,9,9,8,6,6,3,2,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,6,6,3,3,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_485 : RowTree := (.node [12,9,9,8,6,5,3,3,2,2,1,1,1] degreeTree62_483 degreeTree62_484)

def degreeTree62_486 : RowTree := (.node [12,9,9,8,7,3,3,2,2,2,2,1,1,1] (.node [12,9,9,8,6,6,5,1,1,1,1,1,1,1] (.node [12,9,9,8,6,6,4,2,2,1,1,1,1] (.node [12,9,9,8,6,6,4,2,1,1,1,1,1,1] (.node [12,9,9,8,6,6,3,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,8,6,6,4,3,1,1,1,1,1] (.node [12,9,9,8,6,6,4,2,2,2,1,1] .empty .empty) .empty)) (.node [12,9,9,8,7,2,2,2,2,2,2,2,2,1] (.node [12,9,9,8,6,6,6,1,1,1,1,1,1] (.node [12,9,9,8,6,6,5,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,7,3,2,2,2,2,2,2,2] .empty .empty))) (.node [12,9,9,8,7,4,2,2,2,2,2,1,1,1] (.node [12,9,9,8,7,3,3,3,3,1,1,1,1,1] (.node [12,9,9,8,7,3,3,3,2,2,2,1,1] (.node [12,9,9,8,7,3,3,2,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,9,8,7,3,3,3,3,2,2,1] (.node [12,9,9,8,7,3,3,3,3,2,1,1,1] .empty .empty) .empty)) (.node [12,9,9,8,7,4,3,2,2,2,2,1,1] (.node [12,9,9,8,7,4,3,2,2,2,1,1,1,1] (.node [12,9,9,8,7,4,2,2,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,9,8,7,4,3,2,2,2,2,2] .empty .empty))))

def degreeTree62_487 : RowTree := (.node [12,9,9,8,7,4,4,4,1,1,1,1,1] (.node [12,9,9,8,7,4,4,2,2,2,1,1,1] (.node [12,9,9,8,7,4,3,3,3,1,1,1,1] (.node [12,9,9,8,7,4,3,3,2,2,2,1] (.node [12,9,9,8,7,4,3,3,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,7,4,4,2,2,1,1,1,1,1] (.node [12,9,9,8,7,4,3,3,3,2,1,1] .empty .empty) .empty)) (.node [12,9,9,8,7,4,4,3,2,1,1,1,1] (.node [12,9,9,8,7,4,4,3,1,1,1,1,1,1] (.node [12,9,9,8,7,4,4,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,9,8,7,4,4,3,2,2,1,1] .empty .empty))) (.node [12,9,9,8,7,5,3,2,2,2,1,1,1] (.node [12,9,9,8,7,5,2,2,2,2,2,2] (.node [12,9,9,8,7,5,2,2,2,2,2,1,1] (.node [12,9,9,8,7,5,2,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,7,5,3,2,2,1,1,1,1,1] .empty .empty)) (.node [12,9,9,8,7,5,3,3,2,1,1,1,1] (.node [12,9,9,8,7,5,3,3,1,1,1,1,1,1] (.node [12,9,9,8,7,5,3,2,2,2,2,1] .empty .empty) .empty) (.node [12,9,9,8,7,5,3,3,2,2,1,1] .empty .empty))))

def degreeTree62_488 : RowTree := (.node [12,9,9,8,7,4,3,3,2,1,1,1,1,1] degreeTree62_486 degreeTree62_487)

def degreeTree62_489 : RowTree := (.node [12,9,9,8,6,6,3,3,2,1,1,1,1] degreeTree62_485 degreeTree62_488)

def degreeTree62_490 : RowTree := (.node [12,9,9,8,6,4,3,2,2,2,2,2,1] degreeTree62_482 degreeTree62_489)

def degreeTree62_491 : RowTree := (.node [12,9,9,8,7,6,3,2,2,2,1,1] (.node [12,9,9,8,7,6,2,2,2,1,1,1,1,1] (.node [12,9,9,8,7,5,4,3,1,1,1,1,1] (.node [12,9,9,8,7,5,4,2,2,2,1,1] (.node [12,9,9,8,7,5,4,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,7,5,5,2,1,1,1,1,1] (.node [12,9,9,8,7,5,5,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [12,9,9,8,7,6,3,2,1,1,1,1,1,1] (.node [12,9,9,8,7,6,2,2,2,2,2,1] (.node [12,9,9,8,7,6,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,7,6,3,2,2,1,1,1,1] .empty .empty))) (.node [12,9,9,8,7,7,2,2,2,1,1,1,1] (.node [12,9,9,8,7,6,4,2,1,1,1,1,1] (.node [12,9,9,8,7,6,4,1,1,1,1,1,1,1] (.node [12,9,9,8,7,6,3,3,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,7,7,2,2,1,1,1,1,1,1] (.node [12,9,9,8,7,6,5,1,1,1,1,1,1] .empty .empty) .empty)) (.node [12,9,9,8,7,7,3,2,1,1,1,1,1] (.node [12,9,9,8,7,7,3,1,1,1,1,1,1,1] (.node [12,9,9,8,7,7,2,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,8,7,7,4,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_492 : RowTree := (.node [12,9,9,8,8,3,3,3,3,2,1,1] (.node [12,9,9,8,8,3,3,2,2,2,2,2] (.node [12,9,9,8,8,3,2,2,2,2,2,2,1] (.node [12,9,9,8,8,3,2,2,2,2,2,1,1,1] (.node [12,9,9,8,8,2,2,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,9,9,8,8,3,3,2,2,2,2,1,1] (.node [12,9,9,8,8,3,3,2,2,2,1,1,1,1] .empty .empty) .empty)) (.node [12,9,9,8,8,3,3,3,2,2,2,1] (.node [12,9,9,8,8,3,3,3,2,2,1,1,1] (.node [12,9,9,8,8,3,3,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,8,3,3,3,3,1,1,1,1] .empty .empty))) (.node [12,9,9,8,8,4,3,2,2,2,2,1] (.node [12,9,9,8,8,4,2,2,2,2,2,2] (.node [12,9,9,8,8,4,2,2,2,2,2,1,1] (.node [12,9,9,8,8,4,2,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,8,4,3,2,2,2,1,1,1] (.node [12,9,9,8,8,4,3,2,2,1,1,1,1,1] .empty .empty) .empty)) (.node [12,9,9,8,8,4,3,3,2,2,1,1] (.node [12,9,9,8,8,4,3,3,2,1,1,1,1] (.node [12,9,9,8,8,4,3,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,8,4,4,2,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_493 : RowTree := (.node [12,9,9,8,8,2,2,2,2,2,2,2,1,1] degreeTree62_491 degreeTree62_492)

def degreeTree62_494 : RowTree := (.node [12,9,9,8,8,5,4,2,1,1,1,1,1] (.node [12,9,9,8,8,5,3,2,1,1,1,1,1,1] (.node [12,9,9,8,8,5,2,2,2,1,1,1,1,1] (.node [12,9,9,8,8,4,4,3,1,1,1,1,1] (.node [12,9,9,8,8,4,4,2,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,8,8,5,2,2,2,2,2,1] (.node [12,9,9,8,8,5,2,2,2,2,1,1,1] .empty .empty) .empty)) (.node [12,9,9,8,8,5,3,3,1,1,1,1,1] (.node [12,9,9,8,8,5,3,2,2,2,1,1] (.node [12,9,9,8,8,5,3,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,8,5,4,1,1,1,1,1,1,1] .empty .empty))) (.node [12,9,9,8,8,6,3,2,1,1,1,1,1] (.node [12,9,9,8,8,6,2,2,2,1,1,1,1] (.node [12,9,9,8,8,6,2,2,1,1,1,1,1,1] (.node [12,9,9,8,8,5,5,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,8,6,3,1,1,1,1,1,1,1] (.node [12,9,9,8,8,6,2,2,2,2,1,1] .empty .empty) .empty)) (.node [12,9,9,8,8,7,2,2,1,1,1,1,1] (.node [12,9,9,8,8,7,2,1,1,1,1,1,1,1] (.node [12,9,9,8,8,6,4,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,8,8,7,3,1,1,1,1,1,1] .empty .empty))))

def degreeTree62_495 : RowTree := (.node [12,9,9,9,4,4,4,4,2,2,1,1,1] (.node [12,9,9,9,4,4,4,3,2,2,2,1,1] (.node [12,9,9,9,4,4,3,3,3,2,2,1,1] (.node [12,9,9,9,4,4,3,2,2,2,2,2,2] (.node [12,9,9,8,8,8,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,9,4,4,4,2,2,2,2,2,1] (.node [12,9,9,9,4,4,4,2,2,2,2,1,1,1] .empty .empty) .empty)) (.node [12,9,9,9,4,4,4,3,3,2,2,1] (.node [12,9,9,9,4,4,4,3,3,2,1,1,1] (.node [12,9,9,9,4,4,4,3,3,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,9,4,4,4,4,2,1,1,1,1,1] .empty .empty))) (.node [12,9,9,9,5,3,3,3,3,2,2,1,1] (.node [12,9,9,9,4,4,4,4,3,2,1,1] (.node [12,9,9,9,4,4,4,4,3,1,1,1,1] (.node [12,9,9,9,4,4,4,4,2,2,2,1] .empty .empty) .empty) (.node [12,9,9,9,5,3,3,2,2,2,2,2,2] (.node [12,9,9,9,4,4,4,4,4,1,1,1] .empty .empty) .empty)) (.node [12,9,9,9,5,4,3,2,2,2,2,2,1] (.node [12,9,9,9,5,4,3,2,2,2,2,1,1,1] (.node [12,9,9,9,5,4,2,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,9,9,9,5,4,3,3,2,2,2,1,1] .empty .empty))))

def degreeTree62_496 : RowTree := (.node [12,9,9,8,8,8,1,1,1,1,1,1,1,1] degreeTree62_494 degreeTree62_495)

def degreeTree62_497 : RowTree := (.node [12,9,9,8,8,4,4,2,2,1,1,1,1] degreeTree62_493 degreeTree62_496)

def degreeTree62_498 : RowTree := (.node [12,9,9,9,5,4,4,4,1,1,1,1,1,1] (.node [12,9,9,9,5,4,4,3,2,1,1,1,1,1] (.node [12,9,9,9,5,4,4,2,2,2,1,1,1,1] (.node [12,9,9,9,5,4,3,3,3,2,2,1] (.node [12,9,9,9,5,4,3,3,3,2,1,1,1] .empty .empty) .empty) (.node [12,9,9,9,5,4,4,2,2,2,2,2] (.node [12,9,9,9,5,4,4,2,2,2,2,1,1] .empty .empty) .empty)) (.node [12,9,9,9,5,4,4,3,3,1,1,1,1] (.node [12,9,9,9,5,4,4,3,2,2,2,1] (.node [12,9,9,9,5,4,4,3,2,2,1,1,1] .empty .empty) .empty) (.node [12,9,9,9,5,4,4,3,3,2,1,1] .empty .empty))) (.node [12,9,9,9,5,5,3,2,2,2,2,1,1] (.node [12,9,9,9,5,5,2,2,2,2,2,1,1,1] (.node [12,9,9,9,5,4,4,4,2,2,1,1] (.node [12,9,9,9,5,4,4,4,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,9,5,5,3,2,2,2,1,1,1,1] (.node [12,9,9,9,5,5,2,2,2,2,2,2,1] .empty .empty) .empty)) (.node [12,9,9,9,5,5,3,3,2,2,1,1,1] (.node [12,9,9,9,5,5,3,3,2,1,1,1,1,1] (.node [12,9,9,9,5,5,3,2,2,2,2,2] .empty .empty) .empty) (.node [12,9,9,9,5,5,3,3,2,2,2,1] .empty .empty))))

def degreeTree62_499 : RowTree := (.node [12,9,9,9,5,5,5,2,2,2,1,1] (.node [12,9,9,9,5,5,4,3,2,1,1,1,1] (.node [12,9,9,9,5,5,4,2,2,2,1,1,1] (.node [12,9,9,9,5,5,4,2,2,1,1,1,1,1] (.node [12,9,9,9,5,5,3,3,3,2,1,1] .empty .empty) .empty) (.node [12,9,9,9,5,5,4,3,1,1,1,1,1,1] (.node [12,9,9,9,5,5,4,2,2,2,2,1] .empty .empty) .empty)) (.node [12,9,9,9,5,5,5,2,1,1,1,1,1,1] (.node [12,9,9,9,5,5,4,4,1,1,1,1,1] (.node [12,9,9,9,5,5,4,3,2,2,1,1] .empty .empty) .empty) (.node [12,9,9,9,5,5,5,2,2,1,1,1,1] .empty .empty))) (.node [12,9,9,9,6,3,3,3,2,2,2,1,1] (.node [12,9,9,9,6,3,2,2,2,2,2,2,2] (.node [12,9,9,9,6,2,2,2,2,2,2,2,2,1] (.node [12,9,9,9,5,5,5,3,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,9,6,3,3,2,2,2,2,2,1] (.node [12,9,9,9,6,3,3,2,2,2,2,1,1,1] .empty .empty) .empty)) (.node [12,9,9,9,6,3,3,3,3,2,2,1] (.node [12,9,9,9,6,3,3,3,3,2,1,1,1] (.node [12,9,9,9,6,3,3,3,3,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,9,6,4,2,2,2,2,2,1,1,1] .empty .empty))))

def degreeTree62_500 : RowTree := (.node [12,9,9,9,5,5,3,3,3,1,1,1,1] degreeTree62_498 degreeTree62_499)

def degreeTree62_501 : RowTree := (.node [12,9,9,9,6,4,4,2,2,2,2,1] (.node [12,9,9,9,6,4,3,3,2,2,2,1] (.node [12,9,9,9,6,4,3,2,2,2,2,2] (.node [12,9,9,9,6,4,3,2,2,2,2,1,1] (.node [12,9,9,9,6,4,3,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,9,6,4,3,3,2,2,1,1,1] (.node [12,9,9,9,6,4,3,3,2,1,1,1,1,1] .empty .empty) .empty)) (.node [12,9,9,9,6,4,4,2,2,1,1,1,1,1] (.node [12,9,9,9,6,4,3,3,3,2,1,1] (.node [12,9,9,9,6,4,3,3,3,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,9,6,4,4,2,2,2,1,1,1] .empty .empty))) (.node [12,9,9,9,6,5,2,2,2,2,2,1,1] (.node [12,9,9,9,6,4,4,3,2,2,1,1] (.node [12,9,9,9,6,4,4,3,2,1,1,1,1] (.node [12,9,9,9,6,4,4,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,9,6,5,2,2,2,2,1,1,1,1] (.node [12,9,9,9,6,4,4,4,1,1,1,1,1] .empty .empty) .empty)) (.node [12,9,9,9,6,5,3,2,2,2,1,1,1] (.node [12,9,9,9,6,5,3,2,2,1,1,1,1,1] (.node [12,9,9,9,6,5,2,2,2,2,2,2] .empty .empty) .empty) (.node [12,9,9,9,6,5,3,2,2,2,2,1] .empty .empty))))

def degreeTree62_502 : RowTree := (.node [12,9,9,9,6,6,2,2,2,2,2,1] (.node [12,9,9,9,6,5,4,3,1,1,1,1,1] (.node [12,9,9,9,6,5,4,2,1,1,1,1,1,1] (.node [12,9,9,9,6,5,3,3,2,2,1,1] (.node [12,9,9,9,6,5,3,3,2,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,9,6,5,4,2,2,2,1,1] (.node [12,9,9,9,6,5,4,2,2,1,1,1,1] .empty .empty) .empty)) (.node [12,9,9,9,6,6,2,2,2,1,1,1,1,1] (.node [12,9,9,9,6,5,5,2,1,1,1,1,1] (.node [12,9,9,9,6,5,5,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,9,6,6,2,2,2,2,1,1,1] .empty .empty))) (.node [12,9,9,9,6,6,4,1,1,1,1,1,1,1] (.node [12,9,9,9,6,6,3,2,2,2,1,1] (.node [12,9,9,9,6,6,3,2,2,1,1,1,1] (.node [12,9,9,9,6,6,3,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,9,6,6,3,3,1,1,1,1,1] .empty .empty)) (.node [12,9,9,9,7,2,2,2,2,2,2,2,1,1] (.node [12,9,9,9,6,6,5,1,1,1,1,1,1] (.node [12,9,9,9,6,6,4,2,1,1,1,1,1] .empty .empty) .empty) (.node [12,9,9,9,7,2,2,2,2,2,2,2,2] .empty .empty))))

def degreeTree62_503 : RowTree := (.node [12,9,9,9,6,5,3,3,1,1,1,1,1,1] degreeTree62_501 degreeTree62_502)

def degreeTree62_504 : RowTree := (.node [12,9,9,9,6,4,2,2,2,2,2,2,1] degreeTree62_500 degreeTree62_503)

def degreeTree62_505 : RowTree := (.node [12,9,9,9,5,4,3,3,3,1,1,1,1,1] degreeTree62_497 degreeTree62_504)

def degreeTree62_506 : RowTree := (.node [12,9,9,8,7,5,4,2,1,1,1,1,1,1] degreeTree62_490 degreeTree62_505)

def degreeTree62_507 : RowTree := (.node [12,9,9,7,7,5,2,2,2,2,2,1,1,1] degreeTree62_475 degreeTree62_506)

def degreeTree62_508 : RowTree := (.node [12,9,8,8,6,6,3,2,2,2,2,1,1] degreeTree62_444 degreeTree62_507)

def degreeTree62_509 : RowTree := (.node [12,8,8,8,7,5,4,3,2,2,2,1] degreeTree62_381 degreeTree62_508)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan62_0 : PackingPlan := (.join (.twoPaths 13 [8,8,7,7]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 7 3 [9,8]))))

def degreePlan62_1 : PackingPlan := (.join (.twoPaths 13 [8,8,7,7]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 7 2))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeData64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Data 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree64_0 : RowTree := (.node [13,11,10,9,3,2,2,2,2,2,2,2,2,2] (.node [12,11,10,10,3,2,2,2,2,2,2,2,2,2] (.node [11,11,11,10,3,2,2,2,2,2,2,2,2,2] (.node [8,8,8,8,8,8,8,8] .empty .empty) (.node [11,11,11,11,2,2,2,2,2,2,2,2,2,2] .empty .empty)) (.node [12,11,11,10,2,2,2,2,2,2,2,2,2,2] (.node [12,11,11,9,3,2,2,2,2,2,2,2,2,2] .empty .empty) (.node [13,10,10,10,3,2,2,2,2,2,2,2,2,2] .empty .empty))) (.node [13,12,9,9,3,2,2,2,2,2,2,2,2,2] (.node [13,11,11,8,3,2,2,2,2,2,2,2,2,2] (.node [13,11,10,10,2,2,2,2,2,2,2,2,2,2] .empty .empty) (.node [13,11,11,9,2,2,2,2,2,2,2,2,2,2] .empty .empty)) (.node [13,13,9,9,2,2,2,2,2,2,2,2,2,2] (.node [13,13,9,8,3,2,2,2,2,2,2,2,2,2] .empty .empty) (.node [14,11,9,9,3,2,2,2,2,2,2,2,2,2] .empty .empty))))

def degreeTree64 : RowTree := degreeTree64_0

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan64_0 : PackingPlan := (.join (.neighbor 14 [8,7,7,7]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 8 1 [9,8]))))

abbrev degreeP64 := TreeResidual 8 14 degreeQs64 degreeTree64

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan89_0 : PackingPlan := (.join (.twoPaths 17 [10,10,9,9]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 9 3 [11,10])))))

def degreePlan89_1 : PackingPlan := (.join (.twoPaths 17 [10,10,9,9]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 9 2)))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 116. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegions116 : List PrefixRegion := [degreeRegion116_0]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 118. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegions118 : List PrefixRegion := [degreeRegion118_0]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion14_1 : PrefixRegion := ([(6,13)], [(5,11)])

def degreeRegions14 : List PrefixRegion := [degreeRegion14_0,degreeRegion14_1,degreeRegion14_2]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion16_3 : PrefixRegion := ([(5,15)], [(3,9)])
def degreeRegion16_4 : PrefixRegion := ([(5,15)], [(4,12)])

def degreeRegions16 : List PrefixRegion := [degreeRegion16_0,degreeRegion16_1,degreeRegion16_2,degreeRegion16_3,degreeRegion16_4,degreeRegion16_5]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion18_3 : PrefixRegion := ([(5,15)], [(4,12)])
def degreeRegion18_6 : PrefixRegion := ([(6,17)], [(3,9)])
def degreeRegion18_7 : PrefixRegion := ([(6,17)], [(4,12)])
def degreeRegion18_8 : PrefixRegion := ([(6,17)], [(5,15)])

def degreeRegions18 : List PrefixRegion := [degreeRegion18_0,degreeRegion18_1,degreeRegion18_2,degreeRegion18_3,degreeRegion18_4,degreeRegion18_5,degreeRegion18_6,degreeRegion18_7,degreeRegion18_8,degreeRegion18_9]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegions19 : List PrefixRegion := [degreeRegion19_0,degreeRegion19_1]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion20_4 : PrefixRegion := ([(2,9)], [(1,5)])
def degreeRegion20_7 : PrefixRegion := ([(3,13)], [(1,5)])
def degreeRegion20_11 : PrefixRegion := ([(4,16)], [(1,5)])
def degreeRegion20_12 : PrefixRegion := ([(4,16)], [(2,9)])
def degreeRegion20_13 : PrefixRegion := ([(4,16)], [(3,13)])
def degreeRegion20_16 : PrefixRegion := ([(5,19)], [(2,9)])
def degreeRegion20_17 : PrefixRegion := ([(5,19)], [(3,13)])
def degreeRegion20_18 : PrefixRegion := ([(5,19)], [(4,16)])

def degreeRegions20 : List PrefixRegion := [degreeRegion20_0,degreeRegion20_1,degreeRegion20_2,degreeRegion20_3,degreeRegion20_4,degreeRegion20_5,degreeRegion20_6,degreeRegion20_7,degreeRegion20_8,degreeRegion20_9,degreeRegion20_10,degreeRegion20_11,degreeRegion20_12,degreeRegion20_13,degreeRegion20_14,degreeRegion20_15,degreeRegion20_16,degreeRegion20_17,degreeRegion20_18,degreeRegion20_19]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion22_6 : PrefixRegion := ([(5,18)], [(3,12)])
def degreeRegion22_7 : PrefixRegion := ([(5,18)], [(4,15)])
def degreeRegion22_10 : PrefixRegion := ([(6,21)], [(2,8)])
def degreeRegion22_11 : PrefixRegion := ([(6,21)], [(3,12)])
def degreeRegion22_12 : PrefixRegion := ([(6,21)], [(4,15)])
def degreeRegion22_13 : PrefixRegion := ([(6,21)], [(5,18)])

def degreeRegions22 : List PrefixRegion := [degreeRegion22_0,degreeRegion22_1,degreeRegion22_2,degreeRegion22_3,degreeRegion22_4,degreeRegion22_5,degreeRegion22_6,degreeRegion22_7,degreeRegion22_8,degreeRegion22_9,degreeRegion22_10,degreeRegion22_11,degreeRegion22_12,degreeRegion22_13,degreeRegion22_14]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion24_5 : PrefixRegion := ([(2,11)], [(1,7)])
def degreeRegion24_10 : PrefixRegion := ([(3,15)], [(1,7)])
def degreeRegion24_11 : PrefixRegion := ([(3,15)], [(2,11)])
def degreeRegion24_15 : PrefixRegion := ([(4,19)], [(1,7)])
def degreeRegion24_16 : PrefixRegion := ([(4,19)], [(2,11)])
def degreeRegion24_17 : PrefixRegion := ([(4,19)], [(3,15)])
def degreeRegion24_20 : PrefixRegion := ([(5,23)], [(1,7)])
def degreeRegion24_21 : PrefixRegion := ([(5,23)], [(2,11)])
def degreeRegion24_22 : PrefixRegion := ([(5,23)], [(3,15)])
def degreeRegion24_23 : PrefixRegion := ([(5,23)], [(4,19)])

def degreeRegions24 : List PrefixRegion := [degreeRegion24_0,degreeRegion24_1,degreeRegion24_2,degreeRegion24_3,degreeRegion24_4,degreeRegion24_5,degreeRegion24_6,degreeRegion24_7,degreeRegion24_8,degreeRegion24_9,degreeRegion24_10,degreeRegion24_11,degreeRegion24_12,degreeRegion24_13,degreeRegion24_14,degreeRegion24_15,degreeRegion24_16,degreeRegion24_17,degreeRegion24_18,degreeRegion24_19,degreeRegion24_20,degreeRegion24_21,degreeRegion24_22,degreeRegion24_23,degreeRegion24_24]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion26_5 : PrefixRegion := ([(4,18)], [(3,14)])
def degreeRegion26_9 : PrefixRegion := ([(5,22)], [(2,10)])
def degreeRegion26_10 : PrefixRegion := ([(5,22)], [(3,14)])
def degreeRegion26_11 : PrefixRegion := ([(5,22)], [(4,18)])
def degreeRegion26_14 : PrefixRegion := ([(6,25)], [(2,10)])
def degreeRegion26_15 : PrefixRegion := ([(6,25)], [(3,14)])
def degreeRegion26_16 : PrefixRegion := ([(6,25)], [(4,18)])
def degreeRegion26_17 : PrefixRegion := ([(6,25)], [(5,22)])

def degreeRegions26 : List PrefixRegion := [degreeRegion26_0,degreeRegion26_1,degreeRegion26_2,degreeRegion26_3,degreeRegion26_4,degreeRegion26_5,degreeRegion26_6,degreeRegion26_7,degreeRegion26_8,degreeRegion26_9,degreeRegion26_10,degreeRegion26_11,degreeRegion26_12,degreeRegion26_13,degreeRegion26_14,degreeRegion26_15,degreeRegion26_16,degreeRegion26_17,degreeRegion26_18]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion31_5 : PrefixRegion := ([(1,10),(5,22)], [(1,10),(4,18)])
def degreeRegion31_9 : PrefixRegion := ([(1,10),(6,26)], [(1,10),(4,18)])
def degreeRegion31_10 : PrefixRegion := ([(1,10),(6,26)], [(1,10),(5,22)])
def degreeRegion31_13 : PrefixRegion := ([(1,10),(7,30)], [(1,10),(4,18)])
def degreeRegion31_14 : PrefixRegion := ([(1,10),(7,30)], [(1,10),(5,22)])
def degreeRegion31_15 : PrefixRegion := ([(1,10),(7,30)], [(1,10),(6,26)])
def degreeRegion31_17 : PrefixRegion := ([(1,11),(6,26)], [(1,10),(3,14)])
def degreeRegion31_18 : PrefixRegion := ([(1,11),(7,30)], [(1,10),(3,14)])
def degreeRegion31_20 : PrefixRegion := ([(7,30)], [(2,10),(3,14)])

def degreeRegions31 : List PrefixRegion := [degreeRegion31_0,degreeRegion31_1,degreeRegion31_2,degreeRegion31_3,degreeRegion31_4,degreeRegion31_5,degreeRegion31_6,degreeRegion31_7,degreeRegion31_8,degreeRegion31_9,degreeRegion31_10,degreeRegion31_11,degreeRegion31_12,degreeRegion31_13,degreeRegion31_14,degreeRegion31_15,degreeRegion31_16,degreeRegion31_17,degreeRegion31_18,degreeRegion31_19,degreeRegion31_20]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion35_17 : PrefixRegion := ([(1,10),(5,25)], [(1,10),(4,20)])
def degreeRegion35_21 : PrefixRegion := ([(1,10),(6,30)], [(1,10),(4,20)])
def degreeRegion35_22 : PrefixRegion := ([(1,10),(6,30)], [(1,10),(5,25)])
def degreeRegion35_25 : PrefixRegion := ([(1,10),(7,34)], [(1,10),(4,20)])
def degreeRegion35_26 : PrefixRegion := ([(1,10),(7,34)], [(1,10),(5,25)])
def degreeRegion35_27 : PrefixRegion := ([(1,10),(7,34)], [(1,10),(6,30)])
def degreeRegion35_30 : PrefixRegion := ([(1,15),(5,25)], [(1,10),(3,18),(4,20)])
def degreeRegion35_31 : PrefixRegion := ([(1,15),(5,25)], [(1,10),(3,18),(5,25)])
def degreeRegion35_32 : PrefixRegion := ([(1,15),(5,25)], [(1,10),(3,18),(6,30)])
def degreeRegion35_33 : PrefixRegion := ([(1,15),(5,25)], [(1,10),(3,18),(7,34)])
def degreeRegion35_34 : PrefixRegion := ([(1,15),(6,30)], [(1,10),(3,15)])
def degreeRegion35_35 : PrefixRegion := ([(1,15),(6,30)], [(1,10),(3,18),(4,20)])
def degreeRegion35_36 : PrefixRegion := ([(1,15),(6,30)], [(1,10),(3,18),(5,25)])
def degreeRegion35_37 : PrefixRegion := ([(1,15),(6,30)], [(1,10),(3,18),(6,30)])
def degreeRegion35_38 : PrefixRegion := ([(1,15),(6,30)], [(1,10),(3,18),(7,34)])
def degreeRegion35_39 : PrefixRegion := ([(1,15),(7,34)], [(1,10),(3,15)])
def degreeRegion35_40 : PrefixRegion := ([(1,15),(7,34)], [(1,10),(3,18),(4,20)])
def degreeRegion35_41 : PrefixRegion := ([(1,15),(7,34)], [(1,10),(3,18),(5,25)])
def degreeRegion35_42 : PrefixRegion := ([(1,15),(7,34)], [(1,10),(3,18),(6,30)])
def degreeRegion35_43 : PrefixRegion := ([(1,15),(7,34)], [(1,10),(3,18),(7,34)])
def degreeRegion35_45 : PrefixRegion := ([(7,34)], [(2,10),(3,18)])

def degreeRegions35 : List PrefixRegion := [degreeRegion35_0,degreeRegion35_1,degreeRegion35_2,degreeRegion35_3,degreeRegion35_4,degreeRegion35_5,degreeRegion35_6,degreeRegion35_7,degreeRegion35_8,degreeRegion35_9,degreeRegion35_10,degreeRegion35_11,degreeRegion35_12,degreeRegion35_13,degreeRegion35_14,degreeRegion35_15,degreeRegion35_16,degreeRegion35_17,degreeRegion35_18,degreeRegion35_19,degreeRegion35_20,degreeRegion35_21,degreeRegion35_22,degreeRegion35_23,degreeRegion35_24,degreeRegion35_25,degreeRegion35_26,degreeRegion35_27,degreeRegion35_28,degreeRegion35_29,degreeRegion35_30,degreeRegion35_31,degreeRegion35_32,degreeRegion35_33,degreeRegion35_34,degreeRegion35_35,degreeRegion35_36,degreeRegion35_37,degreeRegion35_38,degreeRegion35_39,degreeRegion35_40,degreeRegion35_41,degreeRegion35_42,degreeRegion35_43,degreeRegion35_44,degreeRegion35_45]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData37
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion37_43 : PrefixRegion := ([(1,10),(6,29)], [(1,10),(5,25)])
def degreeRegion37_48 : PrefixRegion := ([(1,10),(7,31)], [(1,10),(5,25)])
def degreeRegion37_49 : PrefixRegion := ([(1,10),(7,31)], [(1,10),(6,29)])
def degreeRegion37_53 : PrefixRegion := ([(1,10),(8,33)], [(1,10),(5,25)])
def degreeRegion37_54 : PrefixRegion := ([(1,10),(8,33)], [(1,10),(6,29)])
def degreeRegion37_55 : PrefixRegion := ([(1,10),(8,33)], [(1,10),(7,31)])
def degreeRegion37_58 : PrefixRegion := ([(1,10),(9,35)], [(1,10),(5,25)])
def degreeRegion37_59 : PrefixRegion := ([(1,10),(9,35)], [(1,10),(6,29)])
def degreeRegion37_60 : PrefixRegion := ([(1,10),(9,35)], [(1,10),(7,31)])
def degreeRegion37_61 : PrefixRegion := ([(1,10),(9,35)], [(1,10),(8,33)])
def degreeRegion37_68 : PrefixRegion := ([(1,17),(3,20),(6,29)], [(1,17),(3,20),(5,25)])
def degreeRegion37_73 : PrefixRegion := ([(1,17),(3,20),(7,31)], [(1,17),(3,20),(5,25)])
def degreeRegion37_74 : PrefixRegion := ([(1,17),(3,20),(7,31)], [(1,17),(3,20),(6,29)])
def degreeRegion37_78 : PrefixRegion := ([(1,17),(3,20),(8,33)], [(1,17),(3,20),(5,25)])
def degreeRegion37_79 : PrefixRegion := ([(1,17),(3,20),(8,33)], [(1,17),(3,20),(6,29)])
def degreeRegion37_80 : PrefixRegion := ([(1,17),(3,20),(8,33)], [(1,17),(3,20),(7,31)])
def degreeRegion37_81 : PrefixRegion := ([(1,17),(3,20),(9,35)], [(1,17),(3,20),(5,25)])
def degreeRegion37_82 : PrefixRegion := ([(1,17),(3,20),(9,35)], [(1,17),(3,20),(6,29)])
def degreeRegion37_83 : PrefixRegion := ([(1,17),(3,20),(9,35)], [(1,17),(3,20),(7,31)])
def degreeRegion37_84 : PrefixRegion := ([(1,17),(5,25)], [(1,10),(3,20),(5,25)])
def degreeRegion37_85 : PrefixRegion := ([(1,17),(5,25)], [(1,10),(3,20),(6,29)])
def degreeRegion37_86 : PrefixRegion := ([(1,17),(5,25)], [(1,10),(3,20),(7,31)])
def degreeRegion37_87 : PrefixRegion := ([(1,17),(5,25)], [(1,10),(3,20),(8,33)])
def degreeRegion37_88 : PrefixRegion := ([(1,17),(5,25)], [(1,10),(3,20),(9,35)])
def degreeRegion37_89 : PrefixRegion := ([(1,17),(5,25)], [(1,10),(3,20),(10,36)])
def degreeRegion37_90 : PrefixRegion := ([(1,17),(5,25)], [(1,10),(4,20)])
def degreeRegion37_91 : PrefixRegion := ([(1,17),(6,29)], [(1,10),(3,20),(5,25)])
def degreeRegion37_92 : PrefixRegion := ([(1,17),(6,29)], [(1,10),(3,20),(6,29)])
def degreeRegion37_93 : PrefixRegion := ([(1,17),(6,29)], [(1,10),(3,20),(7,31)])
def degreeRegion37_94 : PrefixRegion := ([(1,17),(6,29)], [(1,10),(3,20),(8,33)])
def degreeRegion37_95 : PrefixRegion := ([(1,17),(6,29)], [(1,10),(3,20),(9,35)])
def degreeRegion37_96 : PrefixRegion := ([(1,17),(6,29)], [(1,10),(3,20),(10,36)])
def degreeRegion37_97 : PrefixRegion := ([(1,17),(6,29)], [(1,10),(4,20)])
def degreeRegion37_98 : PrefixRegion := ([(1,17),(7,31)], [(1,10),(3,15)])
def degreeRegion37_99 : PrefixRegion := ([(1,17),(7,31)], [(1,10),(3,20),(5,25)])
def degreeRegion37_100 : PrefixRegion := ([(1,17),(7,31)], [(1,10),(3,20),(6,29)])
def degreeRegion37_101 : PrefixRegion := ([(1,17),(7,31)], [(1,10),(3,20),(7,31)])
def degreeRegion37_102 : PrefixRegion := ([(1,17),(7,31)], [(1,10),(3,20),(8,33)])
def degreeRegion37_103 : PrefixRegion := ([(1,17),(7,31)], [(1,10),(3,20),(9,35)])
def degreeRegion37_104 : PrefixRegion := ([(1,17),(7,31)], [(1,10),(3,20),(10,36)])
def degreeRegion37_105 : PrefixRegion := ([(1,17),(7,31)], [(1,10),(4,20)])
def degreeRegion37_106 : PrefixRegion := ([(1,17),(8,33)], [(1,10),(3,15)])
def degreeRegion37_107 : PrefixRegion := ([(1,17),(8,33)], [(1,10),(3,20),(5,25)])
def degreeRegion37_108 : PrefixRegion := ([(1,17),(8,33)], [(1,10),(3,20),(6,29)])
def degreeRegion37_109 : PrefixRegion := ([(1,17),(8,33)], [(1,10),(3,20),(7,31)])
def degreeRegion37_110 : PrefixRegion := ([(1,17),(8,33)], [(1,10),(3,20),(8,33)])
def degreeRegion37_111 : PrefixRegion := ([(1,17),(8,33)], [(1,10),(3,20),(9,35)])
def degreeRegion37_112 : PrefixRegion := ([(1,17),(8,33)], [(1,10),(3,20),(10,36)])
def degreeRegion37_113 : PrefixRegion := ([(1,17),(8,33)], [(1,10),(4,20)])
def degreeRegion37_114 : PrefixRegion := ([(1,17),(9,35)], [(1,10),(3,15)])
def degreeRegion37_115 : PrefixRegion := ([(1,17),(9,35)], [(1,10),(3,20),(5,25)])
def degreeRegion37_116 : PrefixRegion := ([(1,17),(9,35)], [(1,10),(3,20),(6,29)])
def degreeRegion37_117 : PrefixRegion := ([(1,17),(9,35)], [(1,10),(3,20),(7,31)])
def degreeRegion37_118 : PrefixRegion := ([(1,17),(9,35)], [(1,10),(3,20),(8,33)])
def degreeRegion37_119 : PrefixRegion := ([(1,17),(9,35)], [(1,10),(3,20),(9,35)])
def degreeRegion37_120 : PrefixRegion := ([(1,17),(9,35)], [(1,10),(3,20),(10,36)])
def degreeRegion37_121 : PrefixRegion := ([(1,17),(9,35)], [(1,10),(4,20)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData39
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion39_27 : PrefixRegion := ([(1,10),(5,29)], [(1,10),(4,24)])
def degreeRegion39_31 : PrefixRegion := ([(1,10),(6,34)], [(1,10),(2,12)])
def degreeRegion39_32 : PrefixRegion := ([(1,10),(6,34)], [(1,10),(4,24)])
def degreeRegion39_33 : PrefixRegion := ([(1,10),(6,34)], [(1,10),(5,29)])
def degreeRegion39_36 : PrefixRegion := ([(1,10),(7,38)], [(1,10),(2,12)])
def degreeRegion39_37 : PrefixRegion := ([(1,10),(7,38)], [(1,10),(4,24)])
def degreeRegion39_38 : PrefixRegion := ([(1,10),(7,38)], [(1,10),(5,29)])
def degreeRegion39_39 : PrefixRegion := ([(1,10),(7,38)], [(1,10),(6,34)])
def degreeRegion39_45 : PrefixRegion := ([(1,19),(3,22),(5,29)], [(1,19),(3,22),(4,24)])
def degreeRegion39_50 : PrefixRegion := ([(1,19),(3,22),(6,34)], [(1,19),(3,22),(4,24)])
def degreeRegion39_51 : PrefixRegion := ([(1,19),(3,22),(6,34)], [(1,19),(3,22),(5,29)])
def degreeRegion39_55 : PrefixRegion := ([(1,19),(3,22),(7,38)], [(1,19),(3,22),(4,24)])
def degreeRegion39_56 : PrefixRegion := ([(1,19),(3,22),(7,38)], [(1,19),(3,22),(5,29)])
def degreeRegion39_57 : PrefixRegion := ([(1,19),(3,22),(7,38)], [(1,19),(3,22),(6,34)])
def degreeRegion39_60 : PrefixRegion := ([(1,19),(4,24)], [(1,10),(3,22),(4,24)])
def degreeRegion39_61 : PrefixRegion := ([(1,19),(4,24)], [(1,10),(3,22),(5,29)])
def degreeRegion39_62 : PrefixRegion := ([(1,19),(4,24)], [(1,10),(3,22),(6,34)])
def degreeRegion39_63 : PrefixRegion := ([(1,19),(4,24)], [(1,10),(3,22),(7,38)])
def degreeRegion39_64 : PrefixRegion := ([(1,19),(5,29)], [(1,10),(3,18)])
def degreeRegion39_65 : PrefixRegion := ([(1,19),(5,29)], [(1,10),(3,22),(4,24)])
def degreeRegion39_66 : PrefixRegion := ([(1,19),(5,29)], [(1,10),(3,22),(5,29)])
def degreeRegion39_67 : PrefixRegion := ([(1,19),(5,29)], [(1,10),(3,22),(6,34)])
def degreeRegion39_68 : PrefixRegion := ([(1,19),(5,29)], [(1,10),(3,22),(7,38)])
def degreeRegion39_69 : PrefixRegion := ([(1,19),(6,34)], [(1,10),(2,12),(3,22)])
def degreeRegion39_70 : PrefixRegion := ([(1,19),(6,34)], [(1,10),(3,18)])
def degreeRegion39_71 : PrefixRegion := ([(1,19),(6,34)], [(1,10),(3,22),(4,24)])
def degreeRegion39_72 : PrefixRegion := ([(1,19),(6,34)], [(1,10),(3,22),(5,29)])
def degreeRegion39_73 : PrefixRegion := ([(1,19),(6,34)], [(1,10),(3,22),(6,34)])
def degreeRegion39_74 : PrefixRegion := ([(1,19),(6,34)], [(1,10),(3,22),(7,38)])
def degreeRegion39_75 : PrefixRegion := ([(1,19),(7,38)], [(1,10),(2,12),(3,22)])
def degreeRegion39_76 : PrefixRegion := ([(1,19),(7,38)], [(1,10),(3,18)])
def degreeRegion39_77 : PrefixRegion := ([(1,19),(7,38)], [(1,10),(3,22),(4,24)])
def degreeRegion39_78 : PrefixRegion := ([(1,19),(7,38)], [(1,10),(3,22),(5,29)])
def degreeRegion39_79 : PrefixRegion := ([(1,19),(7,38)], [(1,10),(3,22),(6,34)])
def degreeRegion39_80 : PrefixRegion := ([(1,19),(7,38)], [(1,10),(3,22),(7,38)])
def degreeRegion39_82 : PrefixRegion := ([(3,18)], [(1,19),(3,22),(5,29)])
def degreeRegion39_83 : PrefixRegion := ([(3,18)], [(1,19),(3,22),(6,34)])
def degreeRegion39_84 : PrefixRegion := ([(3,18)], [(1,19),(3,22),(7,38)])
def degreeRegion39_85 : PrefixRegion := ([(7,38)], [(2,10),(3,22)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData41
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion41_45 : PrefixRegion := ([(1,10),(6,33)], [(1,10),(5,28)])
def degreeRegion41_50 : PrefixRegion := ([(1,10),(7,35)], [(1,10),(5,28)])
def degreeRegion41_51 : PrefixRegion := ([(1,10),(7,35)], [(1,10),(6,33)])
def degreeRegion41_55 : PrefixRegion := ([(1,10),(8,37)], [(1,10),(5,28)])
def degreeRegion41_56 : PrefixRegion := ([(1,10),(8,37)], [(1,10),(6,33)])
def degreeRegion41_57 : PrefixRegion := ([(1,10),(8,37)], [(1,10),(7,35)])
def degreeRegion41_60 : PrefixRegion := ([(1,10),(9,39)], [(1,10),(5,28)])
def degreeRegion41_61 : PrefixRegion := ([(1,10),(9,39)], [(1,10),(6,33)])
def degreeRegion41_62 : PrefixRegion := ([(1,10),(9,39)], [(1,10),(7,35)])
def degreeRegion41_63 : PrefixRegion := ([(1,10),(9,39)], [(1,10),(8,37)])
def degreeRegion41_72 : PrefixRegion := ([(1,21),(3,24),(6,33)], [(1,21),(3,24),(5,28)])
def degreeRegion41_80 : PrefixRegion := ([(1,21),(3,24),(7,35)], [(1,21),(3,24),(5,28)])
def degreeRegion41_81 : PrefixRegion := ([(1,21),(3,24),(7,35)], [(1,21),(3,24),(6,33)])
def degreeRegion41_88 : PrefixRegion := ([(1,21),(3,24),(8,37)], [(1,21),(3,24),(5,28)])
def degreeRegion41_89 : PrefixRegion := ([(1,21),(3,24),(8,37)], [(1,21),(3,24),(6,33)])
def degreeRegion41_90 : PrefixRegion := ([(1,21),(3,24),(8,37)], [(1,21),(3,24),(7,35)])
def degreeRegion41_95 : PrefixRegion := ([(1,21),(3,24),(9,39)], [(1,21),(3,24),(5,28)])
def degreeRegion41_96 : PrefixRegion := ([(1,21),(3,24),(9,39)], [(1,21),(3,24),(6,33)])
def degreeRegion41_97 : PrefixRegion := ([(1,21),(3,24),(9,39)], [(1,21),(3,24),(7,35)])
def degreeRegion41_98 : PrefixRegion := ([(1,21),(3,24),(9,39)], [(1,21),(3,24),(8,37)])
def degreeRegion41_102 : PrefixRegion := ([(1,21),(3,24),(10,40)], [(1,21),(3,24),(5,28)])
def degreeRegion41_103 : PrefixRegion := ([(1,21),(3,24),(10,40)], [(1,21),(3,24),(6,33)])
def degreeRegion41_104 : PrefixRegion := ([(1,21),(3,24),(10,40)], [(1,21),(3,24),(7,35)])
def degreeRegion41_105 : PrefixRegion := ([(1,21),(3,24),(10,40)], [(1,21),(3,24),(8,37)])
def degreeRegion41_106 : PrefixRegion := ([(1,21),(3,24),(10,40)], [(1,21),(3,24),(9,39)])
def degreeRegion41_109 : PrefixRegion := ([(1,21),(4,23)], [(1,21),(3,24),(5,28)])
def degreeRegion41_110 : PrefixRegion := ([(1,21),(4,23)], [(1,21),(3,24),(6,33)])
def degreeRegion41_111 : PrefixRegion := ([(1,21),(4,23)], [(1,21),(3,24),(7,35)])
def degreeRegion41_112 : PrefixRegion := ([(1,21),(4,23)], [(1,21),(3,24),(8,37)])
def degreeRegion41_113 : PrefixRegion := ([(1,21),(4,23)], [(1,21),(3,24),(9,39)])
def degreeRegion41_114 : PrefixRegion := ([(1,21),(4,23)], [(1,21),(3,24),(10,40)])
def degreeRegion41_115 : PrefixRegion := ([(1,21),(5,28)], [(1,10),(3,24),(5,28)])
def degreeRegion41_116 : PrefixRegion := ([(1,21),(5,28)], [(1,10),(3,24),(6,33)])
def degreeRegion41_117 : PrefixRegion := ([(1,21),(5,28)], [(1,10),(3,24),(7,35)])
def degreeRegion41_118 : PrefixRegion := ([(1,21),(5,28)], [(1,10),(3,24),(8,37)])
def degreeRegion41_119 : PrefixRegion := ([(1,21),(5,28)], [(1,10),(3,24),(9,39)])
def degreeRegion41_120 : PrefixRegion := ([(1,21),(5,28)], [(1,10),(3,24),(10,40)])
def degreeRegion41_121 : PrefixRegion := ([(1,21),(5,28)], [(1,10),(4,23)])
def degreeRegion41_122 : PrefixRegion := ([(1,21),(6,33)], [(1,10),(3,18)])
def degreeRegion41_123 : PrefixRegion := ([(1,21),(6,33)], [(1,10),(3,24),(5,28)])
def degreeRegion41_124 : PrefixRegion := ([(1,21),(6,33)], [(1,10),(3,24),(6,33)])
def degreeRegion41_125 : PrefixRegion := ([(1,21),(6,33)], [(1,10),(3,24),(7,35)])
def degreeRegion41_126 : PrefixRegion := ([(1,21),(6,33)], [(1,10),(3,24),(8,37)])
def degreeRegion41_127 : PrefixRegion := ([(1,21),(6,33)], [(1,10),(3,24),(9,39)])
def degreeRegion41_128 : PrefixRegion := ([(1,21),(6,33)], [(1,10),(3,24),(10,40)])
def degreeRegion41_129 : PrefixRegion := ([(1,21),(6,33)], [(1,10),(4,23)])
def degreeRegion41_130 : PrefixRegion := ([(1,21),(7,35)], [(1,10),(3,18)])
def degreeRegion41_131 : PrefixRegion := ([(1,21),(7,35)], [(1,10),(3,24),(5,28)])
def degreeRegion41_132 : PrefixRegion := ([(1,21),(7,35)], [(1,10),(3,24),(6,33)])
def degreeRegion41_133 : PrefixRegion := ([(1,21),(7,35)], [(1,10),(3,24),(7,35)])
def degreeRegion41_134 : PrefixRegion := ([(1,21),(7,35)], [(1,10),(3,24),(8,37)])
def degreeRegion41_135 : PrefixRegion := ([(1,21),(7,35)], [(1,10),(3,24),(9,39)])
def degreeRegion41_136 : PrefixRegion := ([(1,21),(7,35)], [(1,10),(3,24),(10,40)])
def degreeRegion41_137 : PrefixRegion := ([(1,21),(7,35)], [(1,10),(4,23)])
def degreeRegion41_138 : PrefixRegion := ([(1,21),(8,37)], [(1,10),(3,18)])
def degreeRegion41_139 : PrefixRegion := ([(1,21),(8,37)], [(1,10),(3,24),(5,28)])
def degreeRegion41_140 : PrefixRegion := ([(1,21),(8,37)], [(1,10),(3,24),(6,33)])
def degreeRegion41_141 : PrefixRegion := ([(1,21),(8,37)], [(1,10),(3,24),(7,35)])
def degreeRegion41_142 : PrefixRegion := ([(1,21),(8,37)], [(1,10),(3,24),(8,37)])
def degreeRegion41_143 : PrefixRegion := ([(1,21),(8,37)], [(1,10),(3,24),(9,39)])
def degreeRegion41_144 : PrefixRegion := ([(1,21),(8,37)], [(1,10),(3,24),(10,40)])
def degreeRegion41_145 : PrefixRegion := ([(1,21),(8,37)], [(1,10),(4,23)])
def degreeRegion41_146 : PrefixRegion := ([(1,21),(9,39)], [(1,10),(2,12),(3,24)])
def degreeRegion41_147 : PrefixRegion := ([(1,21),(9,39)], [(1,10),(3,18)])
def degreeRegion41_148 : PrefixRegion := ([(1,21),(9,39)], [(1,10),(3,24),(5,28)])
def degreeRegion41_149 : PrefixRegion := ([(1,21),(9,39)], [(1,10),(3,24),(6,33)])
def degreeRegion41_150 : PrefixRegion := ([(1,21),(9,39)], [(1,10),(3,24),(7,35)])
def degreeRegion41_151 : PrefixRegion := ([(1,21),(9,39)], [(1,10),(3,24),(8,37)])
def degreeRegion41_152 : PrefixRegion := ([(1,21),(9,39)], [(1,10),(3,24),(9,39)])
def degreeRegion41_153 : PrefixRegion := ([(1,21),(9,39)], [(1,10),(3,24),(10,40)])
def degreeRegion41_154 : PrefixRegion := ([(1,21),(9,39)], [(1,10),(4,23)])
def degreeRegion41_155 : PrefixRegion := ([(3,18)], [(1,21),(3,24),(6,33)])
def degreeRegion41_156 : PrefixRegion := ([(3,18)], [(1,21),(3,24),(7,35)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion43_11 : PrefixRegion := ([(1,10),(2,14)], [(1,7)])
def degreeRegion43_20 : PrefixRegion := ([(1,10),(3,20)], [(1,7)])
def degreeRegion43_37 : PrefixRegion := ([(1,10),(4,26)], [(1,7)])
def degreeRegion43_42 : PrefixRegion := ([(1,10),(5,32)], [(1,7)])
def degreeRegion43_43 : PrefixRegion := ([(1,10),(5,32)], [(1,10),(2,14)])
def degreeRegion43_47 : PrefixRegion := ([(1,10),(6,38)], [(1,7)])
def degreeRegion43_48 : PrefixRegion := ([(1,10),(6,38)], [(1,10),(2,14)])
def degreeRegion43_49 : PrefixRegion := ([(1,10),(6,38)], [(1,10),(5,32)])
def degreeRegion43_52 : PrefixRegion := ([(1,10),(7,42)], [(1,10),(2,14)])
def degreeRegion43_53 : PrefixRegion := ([(1,10),(7,42)], [(1,10),(5,32)])
def degreeRegion43_54 : PrefixRegion := ([(1,10),(7,42)], [(1,10),(6,38)])
def degreeRegion43_62 : PrefixRegion := ([(1,23),(3,26),(6,38)], [(1,23),(3,26),(5,32)])
def degreeRegion43_68 : PrefixRegion := ([(1,23),(3,26),(7,42)], [(1,23),(3,26),(5,32)])
def degreeRegion43_69 : PrefixRegion := ([(1,23),(3,26),(7,42)], [(1,23),(3,26),(6,38)])
def degreeRegion43_74 : PrefixRegion := ([(1,23),(4,26)], [(1,7),(3,26)])
def degreeRegion43_75 : PrefixRegion := ([(1,23),(4,26)], [(1,23),(3,26),(5,32)])
def degreeRegion43_76 : PrefixRegion := ([(1,23),(4,26)], [(1,23),(3,26),(6,38)])
def degreeRegion43_77 : PrefixRegion := ([(1,23),(4,26)], [(1,23),(3,26),(7,42)])
def degreeRegion43_80 : PrefixRegion := ([(1,23),(5,32)], [(1,7),(3,26)])
def degreeRegion43_81 : PrefixRegion := ([(1,23),(5,32)], [(1,10),(2,14),(3,26)])
def degreeRegion43_82 : PrefixRegion := ([(1,23),(5,32)], [(1,10),(3,20)])
def degreeRegion43_83 : PrefixRegion := ([(1,23),(5,32)], [(1,10),(3,26),(5,32)])
def degreeRegion43_84 : PrefixRegion := ([(1,23),(5,32)], [(1,10),(3,26),(6,38)])
def degreeRegion43_85 : PrefixRegion := ([(1,23),(5,32)], [(1,10),(3,26),(7,42)])
def degreeRegion43_86 : PrefixRegion := ([(1,23),(5,32)], [(1,10),(4,26)])
def degreeRegion43_87 : PrefixRegion := ([(1,23),(6,38)], [(1,7),(3,26)])
def degreeRegion43_88 : PrefixRegion := ([(1,23),(6,38)], [(1,10),(2,14),(3,26)])
def degreeRegion43_89 : PrefixRegion := ([(1,23),(6,38)], [(1,10),(3,20)])
def degreeRegion43_90 : PrefixRegion := ([(1,23),(6,38)], [(1,10),(3,26),(5,32)])
def degreeRegion43_91 : PrefixRegion := ([(1,23),(6,38)], [(1,10),(3,26),(6,38)])
def degreeRegion43_92 : PrefixRegion := ([(1,23),(6,38)], [(1,10),(3,26),(7,42)])
def degreeRegion43_93 : PrefixRegion := ([(1,23),(6,38)], [(1,10),(4,26)])
def degreeRegion43_94 : PrefixRegion := ([(1,23),(7,42)], [(1,10),(2,14),(3,26)])
def degreeRegion43_95 : PrefixRegion := ([(1,23),(7,42)], [(1,10),(3,20)])
def degreeRegion43_96 : PrefixRegion := ([(1,23),(7,42)], [(1,10),(3,26),(5,32)])
def degreeRegion43_97 : PrefixRegion := ([(1,23),(7,42)], [(1,10),(3,26),(6,38)])
def degreeRegion43_98 : PrefixRegion := ([(1,23),(7,42)], [(1,10),(3,26),(7,42)])
def degreeRegion43_99 : PrefixRegion := ([(1,23),(7,42)], [(1,10),(4,26)])
def degreeRegion43_101 : PrefixRegion := ([(2,14)], [(1,7),(3,26)])
def degreeRegion43_102 : PrefixRegion := ([(2,14)], [(1,10),(2,14),(3,26)])
def degreeRegion43_103 : PrefixRegion := ([(2,14)], [(1,10),(3,20)])
def degreeRegion43_104 : PrefixRegion := ([(2,14)], [(1,10),(3,26),(5,32)])
def degreeRegion43_105 : PrefixRegion := ([(2,14)], [(1,10),(3,26),(6,38)])
def degreeRegion43_106 : PrefixRegion := ([(2,14)], [(1,10),(3,26),(7,42)])
def degreeRegion43_107 : PrefixRegion := ([(2,14)], [(1,10),(4,26)])
def degreeRegion43_108 : PrefixRegion := ([(2,14),(3,26)], [(1,23),(3,26),(5,32)])
def degreeRegion43_109 : PrefixRegion := ([(2,14),(3,26)], [(1,23),(3,26),(6,38)])
def degreeRegion43_110 : PrefixRegion := ([(2,14),(3,26)], [(1,23),(3,26),(7,42)])
def degreeRegion43_111 : PrefixRegion := ([(2,14),(3,26)], [(1,23),(4,26)])
def degreeRegion43_114 : PrefixRegion := ([(3,20)], [(1,7),(3,26)])
def degreeRegion43_115 : PrefixRegion := ([(3,20)], [(1,23),(3,26),(5,32)])
def degreeRegion43_116 : PrefixRegion := ([(3,20)], [(1,23),(3,26),(6,38)])
def degreeRegion43_117 : PrefixRegion := ([(3,20)], [(1,23),(3,26),(7,42)])
def degreeRegion43_118 : PrefixRegion := ([(3,20)], [(2,14),(3,26)])
def degreeRegion43_119 : PrefixRegion := ([(7,42)], [(2,10),(3,26)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData58
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion58_8 : PrefixRegion := ([(1,14),(3,29),(6,42)], [(1,14),(3,29),(5,35)])
def degreeRegion58_16 : PrefixRegion := ([(1,14),(3,29),(7,46)], [(1,14),(3,21)])
def degreeRegion58_17 : PrefixRegion := ([(1,14),(3,29),(7,46)], [(1,14),(3,29),(5,35)])
def degreeRegion58_18 : PrefixRegion := ([(1,14),(3,29),(7,46)], [(1,14),(3,29),(6,42)])
def degreeRegion58_25 : PrefixRegion := ([(1,14),(3,29),(8,49)], [(1,14),(3,21)])
def degreeRegion58_26 : PrefixRegion := ([(1,14),(3,29),(8,49)], [(1,14),(3,29),(5,35)])
def degreeRegion58_27 : PrefixRegion := ([(1,14),(3,29),(8,49)], [(1,14),(3,29),(6,42)])
def degreeRegion58_28 : PrefixRegion := ([(1,14),(3,29),(8,49)], [(1,14),(3,29),(7,46)])
def degreeRegion58_34 : PrefixRegion := ([(1,14),(3,29),(9,52)], [(1,14),(3,29),(5,35)])
def degreeRegion58_35 : PrefixRegion := ([(1,14),(3,29),(9,52)], [(1,14),(3,29),(6,42)])
def degreeRegion58_36 : PrefixRegion := ([(1,14),(3,29),(9,52)], [(1,14),(3,29),(7,46)])
def degreeRegion58_37 : PrefixRegion := ([(1,14),(3,29),(9,52)], [(1,14),(3,29),(8,49)])
def degreeRegion58_42 : PrefixRegion := ([(1,14),(3,29),(10,55)], [(1,14),(3,29),(5,35)])
def degreeRegion58_43 : PrefixRegion := ([(1,14),(3,29),(10,55)], [(1,14),(3,29),(6,42)])
def degreeRegion58_44 : PrefixRegion := ([(1,14),(3,29),(10,55)], [(1,14),(3,29),(7,46)])
def degreeRegion58_45 : PrefixRegion := ([(1,14),(3,29),(10,55)], [(1,14),(3,29),(8,49)])
def degreeRegion58_46 : PrefixRegion := ([(1,14),(3,29),(10,55)], [(1,14),(3,29),(9,52)])
def degreeRegion58_49 : PrefixRegion := ([(1,14),(3,29),(11,57)], [(1,14),(3,29),(6,42)])
def degreeRegion58_50 : PrefixRegion := ([(1,14),(3,29),(11,57)], [(1,14),(3,29),(7,46)])
def degreeRegion58_51 : PrefixRegion := ([(1,14),(3,29),(11,57)], [(1,14),(3,29),(8,49)])
def degreeRegion58_52 : PrefixRegion := ([(1,14),(3,29),(11,57)], [(1,14),(3,29),(9,52)])
def degreeRegion58_53 : PrefixRegion := ([(1,14),(3,29),(11,57)], [(1,14),(3,29),(10,55)])
def degreeRegion58_55 : PrefixRegion := ([(1,14),(4,28)], [(1,14),(3,29),(6,42)])
def degreeRegion58_56 : PrefixRegion := ([(1,14),(4,28)], [(1,14),(3,29),(7,46)])
def degreeRegion58_57 : PrefixRegion := ([(1,14),(4,28)], [(1,14),(3,29),(8,49)])
def degreeRegion58_58 : PrefixRegion := ([(1,14),(4,28)], [(1,14),(3,29),(9,52)])
def degreeRegion58_61 : PrefixRegion := ([(2,14),(3,29),(7,34)], [(1,24),(10,55)])
def degreeRegion58_62 : PrefixRegion := ([(2,14),(3,29),(7,34)], [(1,24),(11,57)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData62
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion62_4 : PrefixRegion := ([(1,14),(2,16),(3,33)], [(1,8),(3,33)])
def degreeRegion62_9 : PrefixRegion := ([(1,14),(3,24)], [(1,8),(3,33)])
def degreeRegion62_10 : PrefixRegion := ([(1,14),(3,24)], [(1,14),(2,16),(3,33)])
def degreeRegion62_27 : PrefixRegion := ([(1,14),(3,33),(6,46)], [(1,14),(3,24)])
def degreeRegion62_28 : PrefixRegion := ([(1,14),(3,33),(6,46)], [(1,14),(3,33),(5,39)])
def degreeRegion62_43 : PrefixRegion := ([(1,14),(3,33),(7,50)], [(1,14),(3,24)])
def degreeRegion62_44 : PrefixRegion := ([(1,14),(3,33),(7,50)], [(1,14),(3,33),(5,39)])
def degreeRegion62_45 : PrefixRegion := ([(1,14),(3,33),(7,50)], [(1,14),(3,33),(6,46)])
def degreeRegion62_52 : PrefixRegion := ([(1,14),(3,33),(8,53)], [(1,14),(3,24)])
def degreeRegion62_53 : PrefixRegion := ([(1,14),(3,33),(8,53)], [(1,14),(3,33),(5,39)])
def degreeRegion62_54 : PrefixRegion := ([(1,14),(3,33),(8,53)], [(1,14),(3,33),(6,46)])
def degreeRegion62_55 : PrefixRegion := ([(1,14),(3,33),(8,53)], [(1,14),(3,33),(7,50)])
def degreeRegion62_61 : PrefixRegion := ([(1,14),(3,33),(9,56)], [(1,14),(2,16),(3,33)])
def degreeRegion62_62 : PrefixRegion := ([(1,14),(3,33),(9,56)], [(1,14),(3,24)])
def degreeRegion62_63 : PrefixRegion := ([(1,14),(3,33),(9,56)], [(1,14),(3,33),(5,39)])
def degreeRegion62_64 : PrefixRegion := ([(1,14),(3,33),(9,56)], [(1,14),(3,33),(6,46)])
def degreeRegion62_65 : PrefixRegion := ([(1,14),(3,33),(9,56)], [(1,14),(3,33),(7,50)])
def degreeRegion62_66 : PrefixRegion := ([(1,14),(3,33),(9,56)], [(1,14),(3,33),(8,53)])
def degreeRegion62_71 : PrefixRegion := ([(1,14),(3,33),(10,59)], [(1,14),(3,24)])
def degreeRegion62_72 : PrefixRegion := ([(1,14),(3,33),(10,59)], [(1,14),(3,33),(5,39)])
def degreeRegion62_73 : PrefixRegion := ([(1,14),(3,33),(10,59)], [(1,14),(3,33),(6,46)])
def degreeRegion62_74 : PrefixRegion := ([(1,14),(3,33),(10,59)], [(1,14),(3,33),(7,50)])
def degreeRegion62_75 : PrefixRegion := ([(1,14),(3,33),(10,59)], [(1,14),(3,33),(8,53)])
def degreeRegion62_76 : PrefixRegion := ([(1,14),(3,33),(10,59)], [(1,14),(3,33),(9,56)])
def degreeRegion62_80 : PrefixRegion := ([(1,14),(3,33),(11,61)], [(1,14),(3,24)])
def degreeRegion62_81 : PrefixRegion := ([(1,14),(3,33),(11,61)], [(1,14),(3,33),(5,39)])
def degreeRegion62_82 : PrefixRegion := ([(1,14),(3,33),(11,61)], [(1,14),(3,33),(6,46)])
def degreeRegion62_83 : PrefixRegion := ([(1,14),(3,33),(11,61)], [(1,14),(3,33),(7,50)])
def degreeRegion62_84 : PrefixRegion := ([(1,14),(3,33),(11,61)], [(1,14),(3,33),(8,53)])
def degreeRegion62_85 : PrefixRegion := ([(1,14),(3,33),(11,61)], [(1,14),(3,33),(9,56)])
def degreeRegion62_86 : PrefixRegion := ([(1,14),(3,33),(11,61)], [(1,14),(3,33),(10,59)])
def degreeRegion62_89 : PrefixRegion := ([(1,14),(4,32)], [(1,8),(3,33)])
def degreeRegion62_90 : PrefixRegion := ([(1,14),(4,32)], [(1,14),(2,16),(3,33)])
def degreeRegion62_91 : PrefixRegion := ([(1,14),(4,32)], [(1,14),(3,24)])
def degreeRegion62_92 : PrefixRegion := ([(1,14),(4,32)], [(1,14),(3,33),(5,39)])
def degreeRegion62_93 : PrefixRegion := ([(1,14),(4,32)], [(1,14),(3,33),(6,46)])
def degreeRegion62_94 : PrefixRegion := ([(1,14),(4,32)], [(1,14),(3,33),(7,50)])
def degreeRegion62_95 : PrefixRegion := ([(1,14),(4,32)], [(1,14),(3,33),(8,53)])
def degreeRegion62_96 : PrefixRegion := ([(1,14),(4,32)], [(1,14),(3,33),(9,56)])
def degreeRegion62_97 : PrefixRegion := ([(1,14),(4,32)], [(1,14),(3,33),(10,59)])
def degreeRegion62_98 : PrefixRegion := ([(1,14),(4,32)], [(1,14),(3,33),(11,61)])
def degreeRegion62_100 : PrefixRegion := ([(1,28),(3,33),(5,39)], [(1,14),(3,33),(7,38)])
def degreeRegion62_101 : PrefixRegion := ([(1,28),(3,33),(6,46)], [(1,14),(3,33),(7,38)])
def degreeRegion62_103 : PrefixRegion := ([(1,28),(3,33),(7,50)], [(1,14),(3,33),(7,38)])
def degreeRegion62_104 : PrefixRegion := ([(1,28),(3,33),(8,53)], [(1,14),(3,33),(7,38)])
def degreeRegion62_105 : PrefixRegion := ([(1,28),(3,33),(9,56)], [(1,14),(3,33),(7,38)])
def degreeRegion62_106 : PrefixRegion := ([(1,28),(3,33),(10,59)], [(1,14),(3,33),(7,38)])
def degreeRegion62_107 : PrefixRegion := ([(1,28),(3,33),(11,61)], [(1,14),(3,33),(7,38)])
def degreeRegion62_110 : PrefixRegion := ([(2,14),(3,33),(7,38)], [(1,28),(10,59)])
def degreeRegion62_111 : PrefixRegion := ([(2,14),(3,33),(7,38)], [(1,28),(11,61)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData64
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion64_3 : PrefixRegion := ([(1,14),(2,16),(3,35)], [(1,8),(3,35)])
def degreeRegion64_6 : PrefixRegion := ([(1,14),(3,24)], [(1,8),(3,35)])
def degreeRegion64_7 : PrefixRegion := ([(1,14),(3,24)], [(1,14),(2,16),(3,35)])
def degreeRegion64_24 : PrefixRegion := ([(1,14),(3,35),(6,45)], [(1,14),(3,35),(5,38)])
def degreeRegion64_43 : PrefixRegion := ([(1,14),(3,35),(7,48)], [(1,14),(3,35),(5,38)])
def degreeRegion64_44 : PrefixRegion := ([(1,14),(3,35),(7,48)], [(1,14),(3,35),(6,45)])
def degreeRegion64_53 : PrefixRegion := ([(1,14),(3,35),(8,51)], [(1,14),(3,24)])
def degreeRegion64_54 : PrefixRegion := ([(1,14),(3,35),(8,51)], [(1,14),(3,35),(5,38)])
def degreeRegion64_55 : PrefixRegion := ([(1,14),(3,35),(8,51)], [(1,14),(3,35),(6,45)])
def degreeRegion64_56 : PrefixRegion := ([(1,14),(3,35),(8,51)], [(1,14),(3,35),(7,48)])
def degreeRegion64_64 : PrefixRegion := ([(1,14),(3,35),(9,54)], [(1,14),(3,24)])
def degreeRegion64_65 : PrefixRegion := ([(1,14),(3,35),(9,54)], [(1,14),(3,35),(5,38)])
def degreeRegion64_66 : PrefixRegion := ([(1,14),(3,35),(9,54)], [(1,14),(3,35),(6,45)])
def degreeRegion64_67 : PrefixRegion := ([(1,14),(3,35),(9,54)], [(1,14),(3,35),(7,48)])
def degreeRegion64_68 : PrefixRegion := ([(1,14),(3,35),(9,54)], [(1,14),(3,35),(8,51)])
def degreeRegion64_75 : PrefixRegion := ([(1,14),(3,35),(10,56)], [(1,14),(3,24)])
def degreeRegion64_76 : PrefixRegion := ([(1,14),(3,35),(10,56)], [(1,14),(3,35),(5,38)])
def degreeRegion64_77 : PrefixRegion := ([(1,14),(3,35),(10,56)], [(1,14),(3,35),(6,45)])
def degreeRegion64_78 : PrefixRegion := ([(1,14),(3,35),(10,56)], [(1,14),(3,35),(7,48)])
def degreeRegion64_79 : PrefixRegion := ([(1,14),(3,35),(10,56)], [(1,14),(3,35),(8,51)])
def degreeRegion64_80 : PrefixRegion := ([(1,14),(3,35),(10,56)], [(1,14),(3,35),(9,54)])
def degreeRegion64_86 : PrefixRegion := ([(1,14),(3,35),(11,58)], [(1,14),(3,24)])
def degreeRegion64_87 : PrefixRegion := ([(1,14),(3,35),(11,58)], [(1,14),(3,35),(5,38)])
def degreeRegion64_88 : PrefixRegion := ([(1,14),(3,35),(11,58)], [(1,14),(3,35),(6,45)])
def degreeRegion64_89 : PrefixRegion := ([(1,14),(3,35),(11,58)], [(1,14),(3,35),(7,48)])
def degreeRegion64_90 : PrefixRegion := ([(1,14),(3,35),(11,58)], [(1,14),(3,35),(8,51)])
def degreeRegion64_91 : PrefixRegion := ([(1,14),(3,35),(11,58)], [(1,14),(3,35),(9,54)])
def degreeRegion64_92 : PrefixRegion := ([(1,14),(3,35),(11,58)], [(1,14),(3,35),(10,56)])
def degreeRegion64_97 : PrefixRegion := ([(1,14),(3,35),(12,60)], [(1,14),(3,24)])
def degreeRegion64_98 : PrefixRegion := ([(1,14),(3,35),(12,60)], [(1,14),(3,35),(5,38)])
def degreeRegion64_99 : PrefixRegion := ([(1,14),(3,35),(12,60)], [(1,14),(3,35),(6,45)])
def degreeRegion64_100 : PrefixRegion := ([(1,14),(3,35),(12,60)], [(1,14),(3,35),(7,48)])
def degreeRegion64_101 : PrefixRegion := ([(1,14),(3,35),(12,60)], [(1,14),(3,35),(8,51)])
def degreeRegion64_102 : PrefixRegion := ([(1,14),(3,35),(12,60)], [(1,14),(3,35),(9,54)])
def degreeRegion64_103 : PrefixRegion := ([(1,14),(3,35),(12,60)], [(1,14),(3,35),(10,56)])
def degreeRegion64_104 : PrefixRegion := ([(1,14),(3,35),(12,60)], [(1,14),(3,35),(11,58)])
def degreeRegion64_108 : PrefixRegion := ([(1,14),(3,35),(13,62)], [(1,14),(3,24)])
def degreeRegion64_109 : PrefixRegion := ([(1,14),(3,35),(13,62)], [(1,14),(3,35),(5,38)])
def degreeRegion64_110 : PrefixRegion := ([(1,14),(3,35),(13,62)], [(1,14),(3,35),(6,45)])
def degreeRegion64_111 : PrefixRegion := ([(1,14),(3,35),(13,62)], [(1,14),(3,35),(7,48)])
def degreeRegion64_112 : PrefixRegion := ([(1,14),(3,35),(13,62)], [(1,14),(3,35),(8,51)])
def degreeRegion64_113 : PrefixRegion := ([(1,14),(3,35),(13,62)], [(1,14),(3,35),(9,54)])
def degreeRegion64_114 : PrefixRegion := ([(1,14),(3,35),(13,62)], [(1,14),(3,35),(10,56)])
def degreeRegion64_115 : PrefixRegion := ([(1,14),(3,35),(13,62)], [(1,14),(3,35),(11,58)])
def degreeRegion64_116 : PrefixRegion := ([(1,14),(3,35),(13,62)], [(1,14),(3,35),(12,60)])
def degreeRegion64_119 : PrefixRegion := ([(1,14),(4,31)], [(1,14),(3,35),(6,45)])
def degreeRegion64_120 : PrefixRegion := ([(1,14),(4,31)], [(1,14),(3,35),(7,48)])
def degreeRegion64_121 : PrefixRegion := ([(1,14),(4,31)], [(1,14),(3,35),(8,51)])
def degreeRegion64_122 : PrefixRegion := ([(1,14),(4,31)], [(1,14),(3,35),(9,54)])
def degreeRegion64_123 : PrefixRegion := ([(1,14),(4,31)], [(1,14),(3,35),(10,56)])
def degreeRegion64_124 : PrefixRegion := ([(1,14),(4,31)], [(1,14),(3,35),(11,58)])
def degreeRegion64_125 : PrefixRegion := ([(1,14),(4,31)], [(1,14),(3,35),(12,60)])
def degreeRegion64_126 : PrefixRegion := ([(1,14),(4,31)], [(1,14),(3,35),(13,62)])
def degreeRegion64_127 : PrefixRegion := ([(1,30),(3,35),(5,38)], [(1,14),(3,35),(7,40)])
def degreeRegion64_128 : PrefixRegion := ([(1,30),(3,35),(6,45)], [(1,14),(3,35),(7,40)])
def degreeRegion64_130 : PrefixRegion := ([(1,30),(3,35),(7,48)], [(1,14),(3,35),(7,40)])
def degreeRegion64_131 : PrefixRegion := ([(1,30),(3,35),(8,51)], [(1,14),(3,35),(7,40)])
def degreeRegion64_132 : PrefixRegion := ([(1,30),(3,35),(9,54)], [(1,14),(3,35),(7,40)])
def degreeRegion64_133 : PrefixRegion := ([(1,30),(3,35),(10,56)], [(1,14),(3,35),(7,40)])
def degreeRegion64_134 : PrefixRegion := ([(1,30),(3,35),(11,58)], [(1,14),(3,35),(7,40)])
def degreeRegion64_135 : PrefixRegion := ([(1,30),(3,35),(12,60)], [(1,14),(3,35),(7,40)])
def degreeRegion64_136 : PrefixRegion := ([(1,30),(3,35),(13,62)], [(1,14),(3,35),(7,40)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegionData89
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Region Data 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion89_4 : PrefixRegion := ([(2,18),(3,44),(5,47)], [(1,10),(2,42),(3,44)])
def degreeRegion89_5 : PrefixRegion := ([(2,18),(3,44),(5,47)], [(1,18),(2,20),(3,44)])
def degreeRegion89_6 : PrefixRegion := ([(2,18),(3,44),(5,47)], [(1,18),(3,30)])
def degreeRegion89_7 : PrefixRegion := ([(2,18),(3,44),(5,47)], [(1,18),(4,40)])

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeSeven
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Seven. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

lemma sevenWitness_card : sevenWitness.card = 7 :=
  diagramOfCols_card _ _ (by simp)

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_FastRowCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Row Check. -/

section

namespace UniversalTensorSquare

def quickBand (M r : ℕ) (rs : List ℕ) : Bool :=
  (List.range 4).any fun k =>
    let d := k+1
    let q := testWidth M d
    decide (d*q+7+d ≤ 2*M-1) && decide (2*M-1 ≤ (rs.take d).sum) &&
      decide (r ≤ ((List.range q).map fun j => (rs.countP (fun a => decide (j < a))-d)/2).sum)

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionStates24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union States 24. -/

section

namespace UniversalTensorSquare

def degreeUnionState24_7 : List PrefixRegion := nextRegions 4 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_8 : List PrefixRegion := nextRegions 5 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_9 : List PrefixRegion := nextRegions 6 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_10 : List PrefixRegion := nextRegions 7 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_11 : List PrefixRegion := nextRegions 8 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_12 : List PrefixRegion := nextRegions 9 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_13 : List PrefixRegion := nextRegions 10 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_14 : List PrefixRegion := nextRegions 11 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_15 : List PrefixRegion := nextRegions 12 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_16 : List PrefixRegion := nextRegions 13 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_17 : List PrefixRegion := nextRegions 14 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_18 : List PrefixRegion := nextRegions 15 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_19 : List PrefixRegion := nextRegions 16 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_20 : List PrefixRegion := nextRegions 17 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_21 : List PrefixRegion := nextRegions 18 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_22 : List PrefixRegion := nextRegions 19 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_23 : List PrefixRegion := nextRegions 20 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_24 : List PrefixRegion := nextRegions 21 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_25 : List PrefixRegion := nextRegions 22 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_26 : List PrefixRegion := nextRegions 23 (liveRegions 6 24 23 degreeHalfRegions24)

def degreeUnionState24_28 : List PrefixRegion := nextRegions 4 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_29 : List PrefixRegion := nextRegions 5 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_30 : List PrefixRegion := nextRegions 6 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_31 : List PrefixRegion := nextRegions 7 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_32 : List PrefixRegion := nextRegions 8 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_33 : List PrefixRegion := nextRegions 9 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_34 : List PrefixRegion := nextRegions 10 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_35 : List PrefixRegion := nextRegions 11 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_36 : List PrefixRegion := nextRegions 12 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_37 : List PrefixRegion := nextRegions 13 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_38 : List PrefixRegion := nextRegions 14 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_39 : List PrefixRegion := nextRegions 15 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_40 : List PrefixRegion := nextRegions 16 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_41 : List PrefixRegion := nextRegions 17 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_42 : List PrefixRegion := nextRegions 18 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_43 : List PrefixRegion := nextRegions 19 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_44 : List PrefixRegion := nextRegions 20 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_45 : List PrefixRegion := nextRegions 21 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_46 : List PrefixRegion := nextRegions 22 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_47 : List PrefixRegion := nextRegions 23 (liveRegions 7 24 23 degreeHalfRegions24)

def degreeUnionState24_49 : List PrefixRegion := nextRegions 3 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_50 : List PrefixRegion := nextRegions 4 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_51 : List PrefixRegion := nextRegions 5 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_52 : List PrefixRegion := nextRegions 6 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_53 : List PrefixRegion := nextRegions 7 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_54 : List PrefixRegion := nextRegions 8 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_55 : List PrefixRegion := nextRegions 9 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_56 : List PrefixRegion := nextRegions 10 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_57 : List PrefixRegion := nextRegions 11 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_58 : List PrefixRegion := nextRegions 12 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_59 : List PrefixRegion := nextRegions 13 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_60 : List PrefixRegion := nextRegions 14 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_61 : List PrefixRegion := nextRegions 15 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_62 : List PrefixRegion := nextRegions 16 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_63 : List PrefixRegion := nextRegions 17 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_64 : List PrefixRegion := nextRegions 18 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_65 : List PrefixRegion := nextRegions 19 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_66 : List PrefixRegion := nextRegions 20 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_67 : List PrefixRegion := nextRegions 21 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_68 : List PrefixRegion := nextRegions 22 (liveRegions 8 24 23 degreeHalfRegions24)

def degreeUnionState24_69 : List PrefixRegion := nextRegions 23 (liveRegions 8 24 23 degreeHalfRegions24)

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionStates26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union States 26. -/

section

namespace UniversalTensorSquare

def degreeUnionState26_8 : List PrefixRegion := nextRegions 4 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_9 : List PrefixRegion := nextRegions 5 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_10 : List PrefixRegion := nextRegions 6 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_11 : List PrefixRegion := nextRegions 7 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_12 : List PrefixRegion := nextRegions 8 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_13 : List PrefixRegion := nextRegions 9 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_14 : List PrefixRegion := nextRegions 10 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_15 : List PrefixRegion := nextRegions 11 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_16 : List PrefixRegion := nextRegions 12 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_17 : List PrefixRegion := nextRegions 13 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_18 : List PrefixRegion := nextRegions 14 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_19 : List PrefixRegion := nextRegions 15 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_20 : List PrefixRegion := nextRegions 16 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_21 : List PrefixRegion := nextRegions 17 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_22 : List PrefixRegion := nextRegions 18 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_23 : List PrefixRegion := nextRegions 19 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_24 : List PrefixRegion := nextRegions 20 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_25 : List PrefixRegion := nextRegions 21 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_26 : List PrefixRegion := nextRegions 22 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_27 : List PrefixRegion := nextRegions 23 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_28 : List PrefixRegion := nextRegions 24 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_29 : List PrefixRegion := nextRegions 25 (liveRegions 7 26 25 degreeHalfRegions26)

def degreeUnionState26_31 : List PrefixRegion := nextRegions 4 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_32 : List PrefixRegion := nextRegions 5 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_33 : List PrefixRegion := nextRegions 6 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_34 : List PrefixRegion := nextRegions 7 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_35 : List PrefixRegion := nextRegions 8 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_36 : List PrefixRegion := nextRegions 9 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_37 : List PrefixRegion := nextRegions 10 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_38 : List PrefixRegion := nextRegions 11 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_39 : List PrefixRegion := nextRegions 12 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_40 : List PrefixRegion := nextRegions 13 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_41 : List PrefixRegion := nextRegions 14 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_42 : List PrefixRegion := nextRegions 15 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_43 : List PrefixRegion := nextRegions 16 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_44 : List PrefixRegion := nextRegions 17 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_45 : List PrefixRegion := nextRegions 18 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_46 : List PrefixRegion := nextRegions 19 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_47 : List PrefixRegion := nextRegions 20 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_48 : List PrefixRegion := nextRegions 21 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_49 : List PrefixRegion := nextRegions 22 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_50 : List PrefixRegion := nextRegions 23 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_51 : List PrefixRegion := nextRegions 24 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_52 : List PrefixRegion := nextRegions 25 (liveRegions 8 26 25 degreeHalfRegions26)

def degreeUnionState26_54 : List PrefixRegion := nextRegions 3 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_55 : List PrefixRegion := nextRegions 4 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_56 : List PrefixRegion := nextRegions 5 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_57 : List PrefixRegion := nextRegions 6 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_58 : List PrefixRegion := nextRegions 7 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_59 : List PrefixRegion := nextRegions 8 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_60 : List PrefixRegion := nextRegions 9 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_61 : List PrefixRegion := nextRegions 10 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_62 : List PrefixRegion := nextRegions 11 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_63 : List PrefixRegion := nextRegions 12 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_64 : List PrefixRegion := nextRegions 13 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_65 : List PrefixRegion := nextRegions 14 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_66 : List PrefixRegion := nextRegions 15 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_67 : List PrefixRegion := nextRegions 16 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_68 : List PrefixRegion := nextRegions 17 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_69 : List PrefixRegion := nextRegions 18 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_70 : List PrefixRegion := nextRegions 19 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_71 : List PrefixRegion := nextRegions 20 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_72 : List PrefixRegion := nextRegions 21 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_73 : List PrefixRegion := nextRegions 22 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_74 : List PrefixRegion := nextRegions 23 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_75 : List PrefixRegion := nextRegions 24 (liveRegions 9 26 25 degreeHalfRegions26)

def degreeUnionState26_76 : List PrefixRegion := nextRegions 25 (liveRegions 9 26 25 degreeHalfRegions26)

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionStates31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union States 31. -/

section

namespace UniversalTensorSquare

def degreeUnionState31_9 : List PrefixRegion := nextRegions 4 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_10 : List PrefixRegion := nextRegions 5 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_11 : List PrefixRegion := nextRegions 6 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_12 : List PrefixRegion := nextRegions 7 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_13 : List PrefixRegion := nextRegions 8 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_14 : List PrefixRegion := nextRegions 9 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_15 : List PrefixRegion := nextRegions 10 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_16 : List PrefixRegion := nextRegions 11 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_17 : List PrefixRegion := nextRegions 12 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_18 : List PrefixRegion := nextRegions 13 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_19 : List PrefixRegion := nextRegions 14 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_20 : List PrefixRegion := nextRegions 15 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_21 : List PrefixRegion := nextRegions 16 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_22 : List PrefixRegion := nextRegions 17 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_23 : List PrefixRegion := nextRegions 18 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_24 : List PrefixRegion := nextRegions 19 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_25 : List PrefixRegion := nextRegions 20 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_26 : List PrefixRegion := nextRegions 21 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_27 : List PrefixRegion := nextRegions 22 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_28 : List PrefixRegion := nextRegions 23 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_29 : List PrefixRegion := nextRegions 24 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_30 : List PrefixRegion := nextRegions 25 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_31 : List PrefixRegion := nextRegions 26 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_32 : List PrefixRegion := nextRegions 27 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_33 : List PrefixRegion := nextRegions 28 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_34 : List PrefixRegion := nextRegions 29 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_35 : List PrefixRegion := nextRegions 30 (liveRegions 8 31 30 degreeHalfRegions31)

def degreeUnionState31_37 : List PrefixRegion := nextRegions 4 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_38 : List PrefixRegion := nextRegions 5 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_39 : List PrefixRegion := nextRegions 6 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_40 : List PrefixRegion := nextRegions 7 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_41 : List PrefixRegion := nextRegions 8 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_42 : List PrefixRegion := nextRegions 9 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_43 : List PrefixRegion := nextRegions 10 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_44 : List PrefixRegion := nextRegions 11 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_45 : List PrefixRegion := nextRegions 12 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_46 : List PrefixRegion := nextRegions 13 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_47 : List PrefixRegion := nextRegions 14 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_48 : List PrefixRegion := nextRegions 15 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_49 : List PrefixRegion := nextRegions 16 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_50 : List PrefixRegion := nextRegions 17 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_51 : List PrefixRegion := nextRegions 18 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_52 : List PrefixRegion := nextRegions 19 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_53 : List PrefixRegion := nextRegions 20 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_54 : List PrefixRegion := nextRegions 21 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_55 : List PrefixRegion := nextRegions 22 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_56 : List PrefixRegion := nextRegions 23 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_57 : List PrefixRegion := nextRegions 24 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_58 : List PrefixRegion := nextRegions 25 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_59 : List PrefixRegion := nextRegions 26 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_60 : List PrefixRegion := nextRegions 27 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_61 : List PrefixRegion := nextRegions 28 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_62 : List PrefixRegion := nextRegions 29 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_63 : List PrefixRegion := nextRegions 30 (liveRegions 9 31 30 degreeHalfRegions31)

def degreeUnionState31_65 : List PrefixRegion := nextRegions 4 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_66 : List PrefixRegion := nextRegions 5 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_67 : List PrefixRegion := nextRegions 6 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_68 : List PrefixRegion := nextRegions 7 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_69 : List PrefixRegion := nextRegions 8 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_70 : List PrefixRegion := nextRegions 9 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_71 : List PrefixRegion := nextRegions 10 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_72 : List PrefixRegion := nextRegions 11 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_73 : List PrefixRegion := nextRegions 12 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_74 : List PrefixRegion := nextRegions 13 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_75 : List PrefixRegion := nextRegions 14 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_76 : List PrefixRegion := nextRegions 15 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_77 : List PrefixRegion := nextRegions 16 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_78 : List PrefixRegion := nextRegions 17 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_79 : List PrefixRegion := nextRegions 18 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_80 : List PrefixRegion := nextRegions 19 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_81 : List PrefixRegion := nextRegions 20 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_82 : List PrefixRegion := nextRegions 21 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_83 : List PrefixRegion := nextRegions 22 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_84 : List PrefixRegion := nextRegions 23 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_85 : List PrefixRegion := nextRegions 24 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_86 : List PrefixRegion := nextRegions 25 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_87 : List PrefixRegion := nextRegions 26 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_88 : List PrefixRegion := nextRegions 27 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_89 : List PrefixRegion := nextRegions 28 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_90 : List PrefixRegion := nextRegions 29 (liveRegions 10 31 30 degreeHalfRegions31)

def degreeUnionState31_91 : List PrefixRegion := nextRegions 30 (liveRegions 10 31 30 degreeHalfRegions31)

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionStates35
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union States 35. -/

section

namespace UniversalTensorSquare

def degreeUnionState35_9 : List PrefixRegion := nextRegions 5 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_10 : List PrefixRegion := nextRegions 6 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_11 : List PrefixRegion := nextRegions 7 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_12 : List PrefixRegion := nextRegions 8 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_13 : List PrefixRegion := nextRegions 9 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_14 : List PrefixRegion := nextRegions 4 (liveRegions 7 26 9 degreeUnionState35_13)

def degreeUnionState35_15 : List PrefixRegion := nextRegions 5 (liveRegions 7 26 9 degreeUnionState35_13)

def degreeUnionState35_16 : List PrefixRegion := nextRegions 6 (liveRegions 7 26 9 degreeUnionState35_13)

def degreeUnionState35_17 : List PrefixRegion := nextRegions 7 (liveRegions 7 26 9 degreeUnionState35_13)

def degreeUnionState35_18 : List PrefixRegion := nextRegions 8 (liveRegions 7 26 9 degreeUnionState35_13)

def degreeUnionState35_19 : List PrefixRegion := nextRegions 9 (liveRegions 7 26 9 degreeUnionState35_13)

def degreeUnionState35_20 : List PrefixRegion := nextRegions 10 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_21 : List PrefixRegion := nextRegions 4 (liveRegions 7 25 10 degreeUnionState35_20)

def degreeUnionState35_22 : List PrefixRegion := nextRegions 5 (liveRegions 7 25 10 degreeUnionState35_20)

def degreeUnionState35_23 : List PrefixRegion := nextRegions 6 (liveRegions 7 25 10 degreeUnionState35_20)

def degreeUnionState35_24 : List PrefixRegion := nextRegions 7 (liveRegions 7 25 10 degreeUnionState35_20)

def degreeUnionState35_25 : List PrefixRegion := nextRegions 8 (liveRegions 7 25 10 degreeUnionState35_20)

def degreeUnionState35_26 : List PrefixRegion := nextRegions 9 (liveRegions 7 25 10 degreeUnionState35_20)

def degreeUnionState35_27 : List PrefixRegion := nextRegions 10 (liveRegions 7 25 10 degreeUnionState35_20)

def degreeUnionState35_28 : List PrefixRegion := nextRegions 11 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_29 : List PrefixRegion := nextRegions 12 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_30 : List PrefixRegion := nextRegions 13 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_31 : List PrefixRegion := nextRegions 14 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_32 : List PrefixRegion := nextRegions 15 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_33 : List PrefixRegion := nextRegions 16 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_34 : List PrefixRegion := nextRegions 17 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_35 : List PrefixRegion := nextRegions 18 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_36 : List PrefixRegion := nextRegions 19 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_37 : List PrefixRegion := nextRegions 20 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_38 : List PrefixRegion := nextRegions 21 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_39 : List PrefixRegion := nextRegions 22 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_40 : List PrefixRegion := nextRegions 23 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_41 : List PrefixRegion := nextRegions 24 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_42 : List PrefixRegion := nextRegions 25 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_43 : List PrefixRegion := nextRegions 26 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_44 : List PrefixRegion := nextRegions 27 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_45 : List PrefixRegion := nextRegions 28 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_46 : List PrefixRegion := nextRegions 29 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_47 : List PrefixRegion := nextRegions 30 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_48 : List PrefixRegion := nextRegions 31 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_49 : List PrefixRegion := nextRegions 32 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_50 : List PrefixRegion := nextRegions 33 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_51 : List PrefixRegion := nextRegions 34 (liveRegions 8 35 34 degreeHalfRegions35)

def degreeUnionState35_53 : List PrefixRegion := nextRegions 4 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_54 : List PrefixRegion := nextRegions 5 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_55 : List PrefixRegion := nextRegions 6 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_56 : List PrefixRegion := nextRegions 7 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_57 : List PrefixRegion := nextRegions 8 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_58 : List PrefixRegion := nextRegions 4 (liveRegions 8 27 8 degreeUnionState35_57)

def degreeUnionState35_59 : List PrefixRegion := nextRegions 5 (liveRegions 8 27 8 degreeUnionState35_57)

def degreeUnionState35_60 : List PrefixRegion := nextRegions 6 (liveRegions 8 27 8 degreeUnionState35_57)

def degreeUnionState35_61 : List PrefixRegion := nextRegions 7 (liveRegions 8 27 8 degreeUnionState35_57)

def degreeUnionState35_62 : List PrefixRegion := nextRegions 8 (liveRegions 8 27 8 degreeUnionState35_57)

def degreeUnionState35_63 : List PrefixRegion := nextRegions 9 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_64 : List PrefixRegion := nextRegions 4 (liveRegions 8 26 9 degreeUnionState35_63)

def degreeUnionState35_65 : List PrefixRegion := nextRegions 5 (liveRegions 8 26 9 degreeUnionState35_63)

def degreeUnionState35_66 : List PrefixRegion := nextRegions 6 (liveRegions 8 26 9 degreeUnionState35_63)

def degreeUnionState35_67 : List PrefixRegion := nextRegions 7 (liveRegions 8 26 9 degreeUnionState35_63)

def degreeUnionState35_68 : List PrefixRegion := nextRegions 8 (liveRegions 8 26 9 degreeUnionState35_63)

def degreeUnionState35_69 : List PrefixRegion := nextRegions 9 (liveRegions 8 26 9 degreeUnionState35_63)

def degreeUnionState35_70 : List PrefixRegion := nextRegions 10 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_71 : List PrefixRegion := nextRegions 4 (liveRegions 8 25 10 degreeUnionState35_70)

def degreeUnionState35_72 : List PrefixRegion := nextRegions 5 (liveRegions 8 25 10 degreeUnionState35_70)

def degreeUnionState35_73 : List PrefixRegion := nextRegions 6 (liveRegions 8 25 10 degreeUnionState35_70)

def degreeUnionState35_74 : List PrefixRegion := nextRegions 7 (liveRegions 8 25 10 degreeUnionState35_70)

def degreeUnionState35_75 : List PrefixRegion := nextRegions 8 (liveRegions 8 25 10 degreeUnionState35_70)

def degreeUnionState35_76 : List PrefixRegion := nextRegions 9 (liveRegions 8 25 10 degreeUnionState35_70)

def degreeUnionState35_77 : List PrefixRegion := nextRegions 10 (liveRegions 8 25 10 degreeUnionState35_70)

def degreeUnionState35_78 : List PrefixRegion := nextRegions 11 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_79 : List PrefixRegion := nextRegions 12 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_80 : List PrefixRegion := nextRegions 13 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_81 : List PrefixRegion := nextRegions 14 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_82 : List PrefixRegion := nextRegions 15 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_83 : List PrefixRegion := nextRegions 16 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_84 : List PrefixRegion := nextRegions 17 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_85 : List PrefixRegion := nextRegions 18 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_86 : List PrefixRegion := nextRegions 19 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_87 : List PrefixRegion := nextRegions 20 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_88 : List PrefixRegion := nextRegions 21 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_89 : List PrefixRegion := nextRegions 22 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_90 : List PrefixRegion := nextRegions 23 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_91 : List PrefixRegion := nextRegions 24 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_92 : List PrefixRegion := nextRegions 25 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_93 : List PrefixRegion := nextRegions 26 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_94 : List PrefixRegion := nextRegions 27 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_95 : List PrefixRegion := nextRegions 28 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_96 : List PrefixRegion := nextRegions 29 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_97 : List PrefixRegion := nextRegions 30 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_98 : List PrefixRegion := nextRegions 31 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_99 : List PrefixRegion := nextRegions 32 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_100 : List PrefixRegion := nextRegions 33 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_101 : List PrefixRegion := nextRegions 34 (liveRegions 9 35 34 degreeHalfRegions35)

def degreeUnionState35_103 : List PrefixRegion := nextRegions 4 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_104 : List PrefixRegion := nextRegions 5 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_105 : List PrefixRegion := nextRegions 6 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_106 : List PrefixRegion := nextRegions 7 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_107 : List PrefixRegion := nextRegions 8 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_108 : List PrefixRegion := nextRegions 3 (liveRegions 9 27 8 degreeUnionState35_107)

def degreeUnionState35_109 : List PrefixRegion := nextRegions 4 (liveRegions 9 27 8 degreeUnionState35_107)

def degreeUnionState35_110 : List PrefixRegion := nextRegions 5 (liveRegions 9 27 8 degreeUnionState35_107)

def degreeUnionState35_111 : List PrefixRegion := nextRegions 6 (liveRegions 9 27 8 degreeUnionState35_107)

def degreeUnionState35_112 : List PrefixRegion := nextRegions 7 (liveRegions 9 27 8 degreeUnionState35_107)

def degreeUnionState35_113 : List PrefixRegion := nextRegions 8 (liveRegions 9 27 8 degreeUnionState35_107)

def degreeUnionState35_114 : List PrefixRegion := nextRegions 9 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_115 : List PrefixRegion := nextRegions 3 (liveRegions 9 26 9 degreeUnionState35_114)

def degreeUnionState35_116 : List PrefixRegion := nextRegions 4 (liveRegions 9 26 9 degreeUnionState35_114)

def degreeUnionState35_117 : List PrefixRegion := nextRegions 5 (liveRegions 9 26 9 degreeUnionState35_114)

def degreeUnionState35_118 : List PrefixRegion := nextRegions 6 (liveRegions 9 26 9 degreeUnionState35_114)

def degreeUnionState35_119 : List PrefixRegion := nextRegions 7 (liveRegions 9 26 9 degreeUnionState35_114)

def degreeUnionState35_120 : List PrefixRegion := nextRegions 8 (liveRegions 9 26 9 degreeUnionState35_114)

def degreeUnionState35_121 : List PrefixRegion := nextRegions 9 (liveRegions 9 26 9 degreeUnionState35_114)

def degreeUnionState35_122 : List PrefixRegion := nextRegions 10 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_123 : List PrefixRegion := nextRegions 3 (liveRegions 9 25 10 degreeUnionState35_122)

def degreeUnionState35_124 : List PrefixRegion := nextRegions 4 (liveRegions 9 25 10 degreeUnionState35_122)

def degreeUnionState35_125 : List PrefixRegion := nextRegions 5 (liveRegions 9 25 10 degreeUnionState35_122)

def degreeUnionState35_126 : List PrefixRegion := nextRegions 6 (liveRegions 9 25 10 degreeUnionState35_122)

def degreeUnionState35_127 : List PrefixRegion := nextRegions 7 (liveRegions 9 25 10 degreeUnionState35_122)

def degreeUnionState35_128 : List PrefixRegion := nextRegions 8 (liveRegions 9 25 10 degreeUnionState35_122)

def degreeUnionState35_129 : List PrefixRegion := nextRegions 9 (liveRegions 9 25 10 degreeUnionState35_122)

def degreeUnionState35_130 : List PrefixRegion := nextRegions 10 (liveRegions 9 25 10 degreeUnionState35_122)

def degreeUnionState35_131 : List PrefixRegion := nextRegions 11 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_132 : List PrefixRegion := nextRegions 12 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_133 : List PrefixRegion := nextRegions 13 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_134 : List PrefixRegion := nextRegions 14 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_135 : List PrefixRegion := nextRegions 15 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_136 : List PrefixRegion := nextRegions 16 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_137 : List PrefixRegion := nextRegions 17 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_138 : List PrefixRegion := nextRegions 18 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_139 : List PrefixRegion := nextRegions 19 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_140 : List PrefixRegion := nextRegions 20 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_141 : List PrefixRegion := nextRegions 21 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_142 : List PrefixRegion := nextRegions 22 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_143 : List PrefixRegion := nextRegions 23 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_144 : List PrefixRegion := nextRegions 24 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_145 : List PrefixRegion := nextRegions 25 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_146 : List PrefixRegion := nextRegions 26 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_147 : List PrefixRegion := nextRegions 27 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_148 : List PrefixRegion := nextRegions 28 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_149 : List PrefixRegion := nextRegions 29 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_150 : List PrefixRegion := nextRegions 30 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_151 : List PrefixRegion := nextRegions 31 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_152 : List PrefixRegion := nextRegions 32 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_153 : List PrefixRegion := nextRegions 33 (liveRegions 10 35 34 degreeHalfRegions35)

def degreeUnionState35_154 : List PrefixRegion := nextRegions 34 (liveRegions 10 35 34 degreeHalfRegions35)

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 112. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan112_1 : PackingPlan := (.join (.twoPaths 19 [11,11,10,10]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 9 2))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree151
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 151. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan151_0 : PackingPlan := (.join (.twoPaths 24 [13,13,13,13]) (.join (.neighbor 11 [6,6,6,5]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 12 3 [14,13])))))))

def degreePlan151_1 : PackingPlan := (.join (.twoPaths 24 [13,13,13,13]) (.join (.neighbor 11 [6,6,6,5]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 12 2)))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan23_0 : PackingPlan := (.join (.twoPaths 5 [4,4,3,3]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 1 2)))

def degreePlan23_1 : PackingPlan := (.join (.repeated 1 7) (.join (.neighbor 4 [3,2,2,2]) (.join (.neighbor 2 [2,1,1,1]) (.repeated 2 1))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan25_0 : PackingPlan := (.join (.neighbor 6 [4,3,3,3]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 2 1 [3,2])))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan27_0 : PackingPlan := (.join (.twoPaths 6 [4,4,4,4]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 2 2)))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan29_0 : PackingPlan := (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 3 1 [4,3])))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree30
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan30_0 : PackingPlan := (.join (.twoPaths 6 [4,4,4,4]) (.join (.neighbor 4 [3,2,2,2]) (.neighbor 2 [2,1,1,1])))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree32
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 32. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan32_0 : PackingPlan := (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 4 [3,2,2,2]) (.join (.repeated 1 3) (.twosOdd 2 1 [3,2]))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree33
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 33. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan33_0 : PackingPlan := (.join (.neighbor 8 [5,4,4,4]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 4 1 [5,4])))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 34. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan34_0 : PackingPlan := (.join (.twoPaths 7 [5,5,4,4]) (.join (.neighbor 4 [3,2,2,2]) (.join (.repeated 1 3) (.repeated 2 2))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree38
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 38. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan38_0 : PackingPlan := (.join (.twoPaths 7 [5,5,4,4]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 1 2))))

def degreePlan38_1 : PackingPlan := (.join (.repeated 1 9) (.join (.neighbor 6 [4,3,3,3]) (.join (.neighbor 4 [3,2,2,2]) (.join (.neighbor 2 [2,1,1,1]) (.repeated 2 1)))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree40
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 40. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan40_0 : PackingPlan := (.join (.neighbor 8 [5,4,4,4]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 2 1 [3,2]))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree42
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 42. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan42_0 : PackingPlan := (.join (.twoPaths 8 [5,5,5,5]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 2 2))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree44
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 44. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan44_0 : PackingPlan := (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 3 1 [4,3]))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree46
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 46. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan46_0 : PackingPlan := (.join (.twoPaths 9 [6,6,5,5]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 3 3 [5,4]))))

def degreePlan46_1 : PackingPlan := (.join (.twoPaths 9 [6,6,5,5]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 3 2))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree47
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 47. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan47_0 : PackingPlan := (.join (.twoPaths 8 [5,5,5,5]) (.join (.neighbor 6 [4,3,3,3]) (.join (.neighbor 4 [3,2,2,2]) (.neighbor 2 [2,1,1,1]))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree48
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 48. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan48_0 : PackingPlan := (.join (.neighbor 10 [6,5,5,5]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 4 1 [5,4]))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree49
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan49_0 : PackingPlan := (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 6 [4,3,3,3]) (.join (.neighbor 4 [3,2,2,2]) (.join (.repeated 1 3) (.twosOdd 2 1 [3,2])))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree50
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan50_0 : PackingPlan := (.join (.twoPaths 10 [6,6,6,6]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 4 3 [6,5]))))

def degreePlan50_1 : PackingPlan := (.join (.twoPaths 10 [6,6,6,6]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 4 2))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree51
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 51. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan51_0 : PackingPlan := (.join (.twoPaths 9 [6,6,5,5]) (.join (.neighbor 6 [4,3,3,3]) (.join (.neighbor 4 [3,2,2,2]) (.join (.repeated 1 3) (.repeated 2 2)))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree52
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 52. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan52_0 : PackingPlan := (.join (.neighbor 11 [6,6,6,5]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 5 1 [6,5]))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree53
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan53_0 : PackingPlan := (.join (.neighbor 10 [6,5,5,5]) (.join (.neighbor 6 [4,3,3,3]) (.join (.neighbor 4 [3,2,2,2]) (.join (.repeated 1 3) (.twosOdd 3 1 [4,3])))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree54
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 54. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan54_0 : PackingPlan := (.join (.twoPaths 11 [7,7,6,6]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 5 3 [7,6]))))

def degreePlan54_1 : PackingPlan := (.join (.twoPaths 11 [7,7,6,6]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 5 2))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree56
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 56. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan56_0 : PackingPlan := (.join (.neighbor 12 [7,6,6,6]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 6 1 [7,6]))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree57
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan57_0 : PackingPlan := (.join (.twoPaths 9 [6,6,5,5]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 1 2)))))

def degreePlan57_1 : PackingPlan := (.join (.repeated 1 11) (.join (.neighbor 8 [5,4,4,4]) (.join (.neighbor 6 [4,3,3,3]) (.join (.neighbor 4 [3,2,2,2]) (.join (.neighbor 2 [2,1,1,1]) (.repeated 2 1))))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree59
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan59_0 : PackingPlan := (.join (.neighbor 10 [6,5,5,5]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 2 1 [3,2])))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree60
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan60_0 : PackingPlan := (.join (.neighbor 13 [7,7,7,6]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 7 1 [8,7]))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree61
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan61_0 : PackingPlan := (.join (.twoPaths 10 [6,6,6,6]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 2 2)))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree63
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 63. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreePlan63_0 : PackingPlan := (.join (.neighbor 11 [6,6,6,5]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 3 1 [4,3])))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_PieriRows116
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pieri Rows 116. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def pieriLower116 : PackingPlan :=
  .join (.threeRows 10 2 [9,8,8]
    [⟨[8,6,6],[8,8,6],[9,8,8]⟩,⟨[8,6,6],[9,7,6],[9,9,7]⟩,⟨[8,6,6],[8,8,6],[10,8,7]⟩,⟨[8,6,6],[9,7,6],[10,9,6]⟩,⟨[10,6,4],[10,7,5],[10,10,5]⟩,⟨[8,6,6],[9,7,6],[11,7,7]⟩,⟨[8,6,6],[8,8,6],[11,8,6]⟩,⟨[8,8,4],[9,8,5],[11,9,5]⟩,⟨[8,8,4],[10,8,4],[11,10,4]⟩,⟨[10,8,2],[11,8,3],[11,11,3]⟩,⟨[8,6,6],[9,7,6],[12,7,6]⟩,⟨[8,8,4],[9,8,5],[12,8,5]⟩,⟨[8,8,4],[10,8,4],[12,9,4]⟩,⟨[10,8,2],[10,9,3],[12,10,3]⟩,⟨[10,8,2],[11,9,2],[12,11,2]⟩,⟨[12,8],[12,9,1],[12,12,1]⟩,⟨[8,6,6],[10,6,6],[13,6,6]⟩,⟨[10,6,4],[10,7,5],[13,7,5]⟩,⟨[8,8,4],[10,8,4],[13,8,4]⟩,⟨[10,8,2],[10,9,3],[13,9,3]⟩,⟨[10,8,2],[10,10,2],[13,10,2]⟩,⟨[10,10],[11,10,1],[13,11,1]⟩,⟨[10,10],[12,10],[13,12]⟩,⟨[10,6,4],[11,6,5],[14,6,5]⟩,⟨[10,6,4],[11,7,4],[14,7,4]⟩,⟨[10,8,2],[11,8,3],[14,8,3]⟩,⟨[10,8,2],[11,9,2],[14,9,2]⟩,⟨[10,10],[11,10,1],[14,10,1]⟩,⟨[10,10],[12,10],[14,11]⟩,⟨[12,4,4],[13,5,4],[15,5,5]⟩,⟨[10,6,4],[12,6,4],[15,6,4]⟩,⟨[12,6,2],[12,7,3],[15,7,3]⟩,⟨[10,8,2],[12,8,2],[15,8,2]⟩,⟨[12,8],[12,9,1],[15,9,1]⟩,⟨[10,10],[12,10],[15,10]⟩,⟨[12,4,4],[13,5,4],[16,5,4]⟩,⟨[12,6,2],[13,6,3],[16,6,3]⟩,⟨[12,6,2],[13,7,2],[16,7,2]⟩,⟨[12,8],[13,8,1],[16,8,1]⟩,⟨[12,8],[13,9],[16,9]⟩,⟨[12,4,4],[14,4,4],[17,4,4]⟩,⟨[14,4,2],[14,5,3],[17,5,3]⟩,⟨[12,6,2],[14,6,2],[17,6,2]⟩,⟨[14,6],[14,7,1],[17,7,1]⟩,⟨[12,8],[14,8],[17,8]⟩,⟨[14,4,2],[15,4,3],[18,4,3]⟩,⟨[14,4,2],[15,5,2],[18,5,2]⟩,⟨[14,6],[15,6,1],[18,6,1]⟩,⟨[14,6],[15,7],[18,7]⟩,⟨[16,2,2],[17,3,2],[19,3,3]⟩,⟨[14,4,2],[16,4,2],[19,4,2]⟩,⟨[16,4],[16,5,1],[19,5,1]⟩,⟨[14,6],[16,6],[19,6]⟩,⟨[16,2,2],[17,3,2],[20,3,2]⟩,⟨[16,4],[17,4,1],[20,4,1]⟩,⟨[16,4],[17,5],[20,5]⟩,⟨[16,2,2],[18,2,2],[21,2,2]⟩,⟨[18,2],[18,3,1],[21,3,1]⟩,⟨[16,4],[18,4],[21,4]⟩,⟨[18,2],[19,2,1],[22,2,1]⟩,⟨[18,2],[19,3],[22,3]⟩,⟨[20],[21,1],[23,1,1]⟩,⟨[18,2],[20,2],[23,2]⟩,⟨[20],[21,1],[24,1]⟩,⟨[20],[22],[25]⟩]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.repeated 1 4))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_PieriRows118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pieri Rows 118. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def pieriLower118 : PackingPlan :=
  .join (.threeRows 11 1 [9,9,8]
    [⟨[8,8,6],[9,8,6],[9,9,8]⟩,⟨[8,8,6],[8,8,7],[10,8,8]⟩,⟨[8,8,6],[9,8,6],[10,9,7]⟩,⟨[10,6,6],[10,7,6],[10,10,6]⟩,⟨[8,8,6],[8,8,7],[11,8,7]⟩,⟨[8,8,6],[9,8,6],[11,9,6]⟩,⟨[10,8,4],[10,8,5],[11,10,5]⟩,⟨[10,8,4],[11,8,4],[11,11,4]⟩,⟨[10,6,6],[10,7,6],[12,7,7]⟩,⟨[8,8,6],[9,8,6],[12,8,6]⟩,⟨[10,8,4],[10,8,5],[12,9,5]⟩,⟨[10,8,4],[10,9,4],[12,10,4]⟩,⟨[10,10,2],[11,10,2],[12,11,3]⟩,⟨[12,8,2],[12,9,2],[12,12,2]⟩,⟨[10,6,6],[10,7,6],[13,7,6]⟩,⟨[10,8,4],[10,8,5],[13,8,5]⟩,⟨[10,8,4],[10,9,4],[13,9,4]⟩,⟨[10,10,2],[10,10,3],[13,10,3]⟩,⟨[10,10,2],[11,10,2],[13,11,2]⟩,⟨[12,10],[12,10,1],[13,12,1]⟩,⟨[12,10],[13,10],[13,13]⟩,⟨[10,6,6],[11,6,6],[14,6,6]⟩,⟨[12,6,4],[12,6,5],[14,7,5]⟩,⟨[10,8,4],[11,8,4],[14,8,4]⟩,⟨[12,8,2],[12,8,3],[14,9,3]⟩,⟨[10,10,2],[11,10,2],[14,10,2]⟩,⟨[12,10],[12,10,1],[14,11,1]⟩,⟨[12,10],[12,11],[14,12]⟩,⟨[12,6,4],[12,6,5],[15,6,5]⟩,⟨[12,6,4],[12,7,4],[15,7,4]⟩,⟨[12,8,2],[12,8,3],[15,8,3]⟩,⟨[12,8,2],[12,9,2],[15,9,2]⟩,⟨[12,10],[12,10,1],[15,10,1]⟩,⟨[12,10],[12,11],[15,11]⟩,⟨[14,4,4],[14,5,4],[16,5,5]⟩,⟨[12,6,4],[13,6,4],[16,6,4]⟩,⟨[14,6,2],[14,6,3],[16,7,3]⟩,⟨[12,8,2],[13,8,2],[16,8,2]⟩,⟨[14,8],[14,8,1],[16,9,1]⟩,⟨[12,10],[13,10],[16,10]⟩,⟨[14,4,4],[14,5,4],[17,5,4]⟩,⟨[14,6,2],[14,6,3],[17,6,3]⟩,⟨[14,6,2],[14,7,2],[17,7,2]⟩,⟨[14,8],[14,8,1],[17,8,1]⟩,⟨[14,8],[14,9],[17,9]⟩,⟨[14,4,4],[15,4,4],[18,4,4]⟩,⟨[16,4,2],[16,4,3],[18,5,3]⟩,⟨[14,6,2],[15,6,2],[18,6,2]⟩,⟨[16,6],[16,6,1],[18,7,1]⟩,⟨[14,8],[15,8],[18,8]⟩,⟨[16,4,2],[16,4,3],[19,4,3]⟩,⟨[16,4,2],[16,5,2],[19,5,2]⟩,⟨[16,6],[16,6,1],[19,6,1]⟩,⟨[16,6],[16,7],[19,7]⟩,⟨[18,2,2],[18,3,2],[20,3,3]⟩,⟨[16,4,2],[17,4,2],[20,4,2]⟩,⟨[18,4],[18,4,1],[20,5,1]⟩,⟨[16,6],[17,6],[20,6]⟩,⟨[18,2,2],[18,3,2],[21,3,2]⟩,⟨[18,4],[18,4,1],[21,4,1]⟩,⟨[18,4],[18,5],[21,5]⟩,⟨[18,2,2],[19,2,2],[22,2,2]⟩,⟨[20,2],[20,2,1],[22,3,1]⟩,⟨[18,4],[19,4],[22,4]⟩,⟨[20,2],[20,2,1],[23,2,1]⟩,⟨[20,2],[20,3],[23,3]⟩,⟨[22],[22,1],[24,1,1]⟩,⟨[20,2],[21,2],[24,2]⟩,⟨[22],[22,1],[25,1]⟩,⟨[22],[23],[26]⟩]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.repeated 1 4))))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ExceptionalFourteen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exceptional Fourteen. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance

def exceptionalPlan71 : PackingPlan := (.join (.neighbor 13 [7,7,7,6]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 5 1 [6,5])))))

def exceptionalPlan73 : PackingPlan := (.join (.twoPaths 13 [8,8,7,7]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 5 3 [7,6])))))

def exceptionalPlan75 : PackingPlan := (.join (.neighbor 14 [8,7,7,7]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 6 1 [7,6])))))

def exceptionalPlan77 : PackingPlan := (.join (.twoPaths 14 [8,8,8,8]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 6 3 [8,7])))))

def exceptionalPlan79 : PackingPlan := (.join (.neighbor 15 [8,8,8,7]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 7 1 [8,7])))))

def exceptionalPlan81 : PackingPlan := (.join (.twoPaths 15 [9,9,8,8]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 7 3 [9,8])))))

def exceptionalPlan83 : PackingPlan := (.join (.neighbor 16 [9,8,8,8]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 8 1 [9,8])))))

def exceptionalPlan85 : PackingPlan := (.join (.twoPaths 16 [9,9,9,9]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 8 3 [10,9])))))

def exceptionalPlan87 : PackingPlan := (.join (.neighbor 17 [9,9,9,8]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 9 1 [10,9])))))

def exceptionalPlan106 : PackingPlan := (.join (.neighbor 18 [10,9,9,9]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 8 1 [9,8]))))))

def exceptionalPlan108 : PackingPlan := (.join (.twoPaths 18 [10,10,10,10]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 8 3 [10,9]))))))

def exceptionalPlan110 : PackingPlan := (.join (.neighbor 19 [10,10,10,9]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 9 1 [10,9]))))))

def exceptionalPlan114 : PackingPlan := (.join (.neighbor 20 [11,10,10,10]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 10 1 [11,10]))))))

def exceptionalPlan149 : PackingPlan := (.join (.neighbor 24 [13,12,12,12]) (.join (.neighbor 11 [6,6,6,5]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 12 1 [13,12])))))))

end UniversalTensorSquare
end
end

end OAI
end



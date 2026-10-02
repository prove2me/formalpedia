-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_Batch000__11_q04_q02
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_Batch000__11_q04_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T01:10:10.540913+00:00
-- url     : https://prove2.me/theorems/b965ee55-6d91-4eb6-b730-cb35758a474f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch000 (+10 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch001, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch000 (+10 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch001, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch002, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch003, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch004, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch005, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch006, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch007, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch008, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch009, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch010) (piece 5 of 11) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch000 (+10 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch001, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch002, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch003, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch004, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch005, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch006, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch007, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch008, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch009, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch010) (piece 5 of 11) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch000 (+10 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch001, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch002, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch003, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch004, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch005, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch006, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch007, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch008, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch009, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch010) (piece 5 of 11) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch000 (+10 modules: GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch001, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch002, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch003, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch004, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch005, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch006, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch007, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch008, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch009, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch010) (piece 5 of 11) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_Batch000__11_q04_q01

namespace GeneralCK.Certificates.E8TAxisFullBridge.Batch004
open E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem historical_rectangle_0149 : (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), 0, (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisZero0048Root.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisZero0048Root.rectangle, GeneralCK.Certificates.E8TAxisZero0048Root.rationalRectangle]

theorem historical_positive_0149 : CellPositive (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), 0, (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0149]
  exact GeneralCK.Certificates.E8TAxisZero0048Root.cellPositive

theorem historical_index_0150 : cells[150]? = some (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0150 : (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0205.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0205.rectangle]

theorem historical_positive_0150 : CellPositive (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0150]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0205.cellPositive

theorem historical_index_0151 : cells[151]? = some (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0151 : (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0199.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0199.rectangle]

theorem historical_positive_0151 : CellPositive (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0151]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0199.cellPositive

theorem historical_index_0152 : cells[152]? = some (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0152 : (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0197.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0197.rectangle]

theorem historical_positive_0152 : CellPositive (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0152]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0197.cellPositive

theorem historical_index_0153 : cells[153]? = some (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0153 : (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0179.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0179.rectangle]

theorem historical_positive_0153 : CellPositive (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0153]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0179.cellPositive

theorem historical_index_0154 : cells[154]? = some (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0154 : (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0177.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0177.rectangle]

theorem historical_positive_0154 : CellPositive (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0154]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0177.cellPositive

theorem historical_index_0155 : cells[155]? = some (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0155 : (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0171.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0171.rectangle]

theorem historical_positive_0155 : CellPositive (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0155]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0171.cellPositive

theorem historical_index_0156 : cells[156]? = some (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (1 / 50 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0156 : (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (1 / 50 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0169.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0169.rectangle]

theorem historical_positive_0156 : CellPositive (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (1 / 50 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0156]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0169.cellPositive

theorem historical_index_0157 : cells[157]? = some (⟨(19 / 16 : ℚ), (5 / 4 : ℚ), 0, (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0157 : (⟨(19 / 16 : ℚ), (5 / 4 : ℚ), 0, (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisZero0047Root.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisZero0047Root.rectangle, GeneralCK.Certificates.E8TAxisZero0047Root.rationalRectangle]

theorem historical_positive_0157 : CellPositive (⟨(19 / 16 : ℚ), (5 / 4 : ℚ), 0, (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0157]
  exact GeneralCK.Certificates.E8TAxisZero0047Root.cellPositive

theorem historical_index_0158 : cells[158]? = some (⟨(19 / 16 : ℚ), (5 / 4 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0158 : (⟨(19 / 16 : ℚ), (5 / 4 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0204.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0204.rectangle]

theorem historical_positive_0158 : CellPositive (⟨(19 / 16 : ℚ), (5 / 4 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0158]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0204.cellPositive

theorem historical_index_0159 : cells[159]? = some (⟨(19 / 16 : ℚ), (5 / 4 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0159 : (⟨(19 / 16 : ℚ), (5 / 4 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0198.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0198.rectangle]

theorem historical_positive_0159 : CellPositive (⟨(19 / 16 : ℚ), (5 / 4 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0159]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0198.cellPositive

end GeneralCK.Certificates.E8TAxisFullBridge.Batch004



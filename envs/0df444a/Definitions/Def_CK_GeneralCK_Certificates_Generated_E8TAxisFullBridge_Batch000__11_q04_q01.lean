-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_Batch000__11_q04_q01
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_Batch000__11_q04_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T21:26:57.50837+00:00
-- url     : https://prove2.me/theorems/8db89ebe-dee5-44f1-9ef6-2fec845f2c4b
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch000 (+10 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch001, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch000 (+10 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch001, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch002, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch003, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch004, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch005, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch006, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch007, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch008, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch009, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch010) (piece 5 of 11) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch000 (+10 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch001, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch002, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch003, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch004, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch005, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch006, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch007, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch008, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch009, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch010) (piece 5 of 11) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch000 (+10 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch001, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch002, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch003, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch004, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch005, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch006, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch007, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch008, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch009, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch010) (piece 5 of 11) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch000 (+10 modules: GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch001, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch002, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch003, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch004, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch005, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch006, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch007, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch008, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch009, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch010) (piece 5 of 11) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_Batch000__11_q04_q00

namespace GeneralCK.Certificates.E8TAxisFullBridge.Batch004
open E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem historical_positive_0138 : CellPositive (⟨1, (17 / 16 : ℚ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0138]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0181.cellPositive

theorem historical_index_0139 : cells[139]? = some (⟨1, (17 / 16 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0139 : (⟨1, (17 / 16 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0175.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0175.rectangle]

theorem historical_positive_0139 : CellPositive (⟨1, (17 / 16 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0139]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0175.cellPositive

theorem historical_index_0140 : cells[140]? = some (⟨1, (17 / 16 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (1 / 50 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0140 : (⟨1, (17 / 16 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (1 / 50 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0173.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0173.rectangle]

theorem historical_positive_0140 : CellPositive (⟨1, (17 / 16 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (1 / 50 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0140]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0173.cellPositive

theorem historical_index_0141 : cells[141]? = some (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), 0, (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0141 : (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), 0, (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisZero0049Root.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisZero0049Root.rectangle, GeneralCK.Certificates.E8TAxisZero0049Root.rationalRectangle]

theorem historical_positive_0141 : CellPositive (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), 0, (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0141]
  exact GeneralCK.Certificates.E8TAxisZero0049Root.cellPositive

theorem historical_index_0142 : cells[142]? = some (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0142 : (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0206.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0206.rectangle]

theorem historical_positive_0142 : CellPositive (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0142]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0206.cellPositive

theorem historical_index_0143 : cells[143]? = some (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0143 : (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0202.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0202.rectangle]

theorem historical_positive_0143 : CellPositive (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0143]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0202.cellPositive

theorem historical_index_0144 : cells[144]? = some (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0144 : (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0200.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0200.rectangle]

theorem historical_positive_0144 : CellPositive (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (18749999999999999999999999999999999999999999999999999999999502158777771 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0144]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0200.cellPositive

theorem historical_index_0145 : cells[145]? = some (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0145 : (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0182.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0182.rectangle]

theorem historical_positive_0145 : CellPositive (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0145]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0182.cellPositive

theorem historical_index_0146 : cells[146]? = some (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0146 : (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0180.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0180.rectangle]

theorem historical_positive_0146 : CellPositive (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (3124999999999999999999999999999999999999999999999999999999502158777771 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0146]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0180.cellPositive

theorem historical_index_0147 : cells[147]? = some (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0147 : (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0174.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0174.rectangle]

theorem historical_positive_0147 : CellPositive (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0147]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0174.cellPositive

theorem historical_index_0148 : cells[148]? = some (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (1 / 50 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0148 : (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (1 / 50 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0172.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0172.rectangle]

theorem historical_positive_0148 : CellPositive (⟨(17 / 16 : ℚ), (9 / 8 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (1 / 50 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0148]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0172.cellPositive

theorem historical_index_0149 : cells[149]? = some (⟨(9 / 8 : ℚ), (19 / 16 : ℚ), 0, (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

end GeneralCK.Certificates.E8TAxisFullBridge.Batch004



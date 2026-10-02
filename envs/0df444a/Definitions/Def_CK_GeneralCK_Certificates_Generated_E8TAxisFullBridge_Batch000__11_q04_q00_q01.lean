-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_Batch000__11_q04_q00_q01
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_Batch000__11_q04_q00_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T19:00:11.296282+00:00
-- url     : https://prove2.me/theorems/37ab3ba3-57d9-4e97-9dc9-58d8e2afaed6
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch000 (+10 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch001, GeneralCK.Certificates.…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch000 (+10 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch001, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch002, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch003, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch004, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch005, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch006, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch007, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch008, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch009, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch010) (piece 5 of 11) (piece 1 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch000 (+10 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch001, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch002, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch003, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch004, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch005, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch006, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch007, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch008, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch009, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch010) (piece 5 of 11) (piece 1 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch000 (+10 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch001, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch002, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch003, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch004, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch005, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch006, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch007, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch008, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch009, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch010) (piece 5 of 11) (piece 1 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch000 (+10 modules: GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch001, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch002, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch003, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch004, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch005, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch006, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch007, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch008, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch009, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch010) (piece 5 of 11) (piece 1 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_Batch000__11_q04_q00_q00

namespace GeneralCK.Certificates.E8TAxisFullBridge.Batch004
open E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem historical_rectangle_0131 : (⟨(15 / 16 : ℚ), 1, (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0059.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0059.rectangle]

theorem historical_positive_0131 : CellPositive (⟨(15 / 16 : ℚ), 1, (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0131]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0059.cellPositive

theorem historical_index_0132 : cells[132]? = some (⟨(15 / 16 : ℚ), 1, (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (1 / 50 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0132 : (⟨(15 / 16 : ℚ), 1, (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (1 / 50 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0057.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0057.rectangle]

theorem historical_positive_0132 : CellPositive (⟨(15 / 16 : ℚ), 1, (14999999999999999999999999999999999999999999999999999999999601727022217 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (1 / 50 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0132]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0057.cellPositive

theorem historical_index_0133 : cells[133]? = some (⟨1, (17 / 16 : ℚ), 0, (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0133 : (⟨1, (17 / 16 : ℚ), 0, (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisZero0050Root.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisZero0050Root.rectangle, GeneralCK.Certificates.E8TAxisZero0050Root.rationalRectangle]

theorem historical_positive_0133 : CellPositive (⟨1, (17 / 16 : ℚ), 0, (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0133]
  exact GeneralCK.Certificates.E8TAxisZero0050Root.cellPositive

theorem historical_index_0134 : cells[134]? = some (⟨1, (17 / 16 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

theorem historical_rectangle_0134 : (⟨1, (17 / 16 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0207.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0207.rectangle]

end GeneralCK.Certificates.E8TAxisFullBridge.Batch004



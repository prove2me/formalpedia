-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_Batch011__10_q01_q00_q01_q02
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_Batch011__10_q01_q00_q01_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T06:06:08.135899+00:00
-- url     : https://prove2.me/theorems/648b1108-8a44-45e1-8556-7bbdd7a5abfa
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch011 (+9 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch012, GeneralCK.Certificates.G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch011 (+9 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch012, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch013, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch014, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch015, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch016, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch017, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch018, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch019, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch020) (piece 2 of 10) (piece 1 of 4) (piece 2 of 4) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch011 (+9 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch012, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch013, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch014, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch015, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch016, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch017, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch018, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch019, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch020) (piece 2 of 10) (piece 1 of 4) (piece 2 of 4) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch011 (+9 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch012, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch013, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch014, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch015, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch016, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch017, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch018, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch019, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch020) (piece 2 of 10) (piece 1 of 4) (piece 2 of 4) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch011 (+9 modules: GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch012, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch013, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch014, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch015, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch016, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch017, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch018, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch019, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch020) (piece 2 of 10) (piece 1 of 4) (piece 2 of 4) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_Batch011__10_q01_q00_q01_q01

namespace GeneralCK.Certificates.E8TAxisFullBridge.Batch012
open E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem historical_rectangle_0389 : (⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), 0, (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real = GeneralCK.Certificates.E8TAxisZero0074Root.rectangle := by
  norm_num [RatRect.real, GeneralCK.Certificates.E8TAxisZero0074Root.rectangle, GeneralCK.Certificates.E8TAxisZero0074Root.rationalRectangle]

theorem historical_positive_0389 : CellPositive (⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), 0, (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0389]
  exact GeneralCK.Certificates.E8TAxisZero0074Root.cellPositive

theorem historical_index_0390 : cells[390]? = some (⟨(5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (11617187499999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect) := by
  decide +kernel

end GeneralCK.Certificates.E8TAxisFullBridge.Batch012



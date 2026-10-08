-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_Batch011__10_q01_q00_q00_q02
-- name    : CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_Batch011__10_q01_q00_q00_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T01:33:47.514006+00:00
-- url     : https://prove2.me/theorems/4c2c6a92-4297-4a8b-9f25-15fcae88ccc7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch011 (+9 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch012, GeneralCK.Certificates.G…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch011 (+9 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch012, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch013, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch014, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch015, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch016, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch017, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch018, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch019, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch020) (piece 2 of 10) (piece 1 of 4) (piece 1 of 4) (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch011 (+9 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch012, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch013, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch014, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch015, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch016, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch017, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch018, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch019, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch020) (piece 2 of 10) (piece 1 of 4) (piece 1 of 4) (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch011 (+9 modules: GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch012, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch013, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch014, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch015, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch016, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch017, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch018, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch019, GeneralCK.Certificates.Generated.E8TAxisFullBridge.Batch020) (piece 2 of 10) (piece 1 of 4) (piece 1 of 4) (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch011 (+9 modules: GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch012, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch013, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch014, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch015, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch016, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch017, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch018, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch019, GeneralCK/Certificates/Generated/E8TAxisFullBridge/Batch020) (piece 2 of 10) (piece 1 of 4) (piece 1 of 4) (piece 3 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_E8TAxisFullBridge_Batch011__10_q01_q00_q00_q02_q01

namespace GeneralCK.Certificates.E8TAxisFullBridge.Batch012
open E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
theorem historical_positive_0386 : CellPositive (⟨(11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (16250000000000000000000000000000000000000000000000000000000398272977783 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (17500000000000000000000000000000000000000000000000000000001194818933349 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩ : RatRect).real := by
  rw [historical_rectangle_0386]
  exact GeneralCK.Certificates.E8TAxisPositiveAggregation.Root0520.cellPositive

end GeneralCK.Certificates.E8TAxisFullBridge.Batch012



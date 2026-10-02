-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T05:41:00.563596+00:00
-- url     : https://prove2.me/theorems/ed15ad2e-9402-4196-a223-543f9c556a04
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddleAggregation (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddleAggregation.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddleAggregation_part01
namespace GeneralCK.Certificates.DoubleCapMiddle
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem doubleCapMiddleAggregation :
    (∀ m, 1/5 ≤ m → m ≤ 1/4 → 0 ≤ doubleCapLowResidual m) ∧
    (∀ m, 1/4 ≤ m → m ≤ 2/5 → 0 ≤ doubleCapHighResidual m) :=
  ⟨doubleCapLowResidual_middle, doubleCapHighResidual_middle⟩

#print axioms doubleCapMiddleAggregation
end GeneralCK.Certificates.DoubleCapMiddle



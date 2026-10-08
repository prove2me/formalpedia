-- Prove2me | Definitions.Def_CK_CKLaneA4_D2Slot_q02
-- name    : CK_CKLaneA4_D2Slot_q02
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T04:56:16.395557+00:00
-- url     : https://prove2.me/theorems/843606bc-34c1-4d70-8b36-09b665e9c2c3
-- title:
--   Courtade–Kumar proof module `CKLaneA4.D2Slot (piece 3 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA4.D2Slot (piece 3 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA4.D2Slot (piece 3 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA4.D2Slot (piece 3 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA4/D2Slot (piece 3 of 4).lean)

import Definitions.Def_CK_CKLaneA4_D2Slot_q01

namespace CKLaneA4.D2
open GeneralCK GeneralCK.Correction GeneralCK.Correction.Complement CKLaneA.Cell CKLaneA.Prog
/-- the `1/10 < u ≤ 1/5, rho < 1/10` arm of `OutsideCertifiedC1C2Region`, strict form -/
theorem diagonal2_arm : ∀ ⦃u rho : ℝ⦄, 0 < u → u < 1 / 2 → 0 < rho → rho < 1 →
    1 / 10 < u → u ≤ 1 / 5 → rho < 1 / 10 → ActualRatioMinorsPositive u rho := by
  intro u rho _ _ hr _ h10 h5 h1
  exact diagonal2_actual ⟨h10.le, h5⟩ ⟨hr, h1.le⟩

end CKLaneA4.D2



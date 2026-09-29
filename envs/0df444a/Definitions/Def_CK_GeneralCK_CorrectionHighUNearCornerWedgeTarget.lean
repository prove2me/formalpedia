-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerWedgeTarget
-- name    : CK_GeneralCK_CorrectionHighUNearCornerWedgeTarget
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:48:06.729719+00:00
-- url     : https://prove2.me/theorems/a7331821-f323-48c1-9ab3-ef54cb6de39c
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionHighUNearCornerWedgeTarget` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionHighUNearCornerWedgeTarget` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionHighUNearCornerWedgeTarget` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionHighUNearCornerWedgeTarget (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHighUNearCornerWedgeTarget.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHighUScaledContract

/-!
# Source-only two-wedge target for the correction high-u corner

The raw lower bounds split at `rho=t` and avoid dividing by powers
that vanish on the open coordinate faces. No bound is proved here.
-/

namespace GeneralCK.Correction.HighU

def NearCornerRawWedgeTarget : Prop :=
  ∀ t rho : ℝ, 0 < t → t ≤ 1 / 100 → 0 < rho → rho ≤ 1 / 100 →
    t ^ 2 / 2 ≤ Natural.m11 (1 / 2 - t) (1 / 2 - (1 - rho) * t) ∧
    (rho ≤ t →
      2 * rho ^ 2 * t ^ 9 ≤
        Natural.kdet (1 / 2 - t) (1 / 2 - (1 - rho) * t)) ∧
    (t ≤ rho →
      2 * rho ^ 4 * t ^ 7 ≤
        Natural.kdet (1 / 2 - t) (1 / 2 - (1 - rho) * t))

end GeneralCK.Correction.HighU



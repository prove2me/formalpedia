-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8LineAnchorInverseBridge
-- name    : CK_GeneralCK_Certificates_E8LineAnchorInverseBridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:01:29.767784+00:00
-- url     : https://prove2.me/theorems/d7d3aed9-3488-4ecb-b6ec-64e0cfc348bd
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8LineAnchorInverseBridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8LineAnchorInverseBridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8LineAnchorInverseBridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8LineAnchorInverseBridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8LineAnchorInverseBridge.lean)

import Definitions.Def_CK_GeneralCK_Certificates_Jet2
import Definitions.Def_CK_GeneralCK_Certificates_E8ThetaHigherDerivatives

-- ===== source module GeneralCK.Certificates.E8LineAnchorInverseBridge =====
section

/-! The unconditional first/second-order bridge from the concrete `e8Q` to
the inverse recurrence. Higher orders still require derivatives of `e8Theta`. -/

namespace GeneralCK.Certificates.E8LineAnchorInverseBridge

open GeneralCK

/-- The first two derivatives of the concrete inverse, expressed in terms of
the corresponding derivatives of `e8Theta`. -/
noncomputable def e8QSecondJet : Jet2 where
  value := e8Q
  first := deriv e8Q
  second := fun y =>
    -deriv (deriv e8Theta) (e8Q y) / (deriv e8Theta (e8Q y)) ^ 3

/-- A local second derivative of `e8Theta` is the sole explicit analytic
premise. The inverse construction and both `e8Q` derivative identities are
then proved by the existing sound inverse theorems. -/
theorem e8QSecondJet_soundAt {y theta2 : ℝ} (hy : y ∈ e8SlopeRange)
    (hθ2 : HasDerivAt (deriv e8Theta) theta2 (e8Q y)) :
    e8QSecondJet.SoundAt y := by
  have hq1 := hasDerivAt_e8Q hy
  have hq2 := hasDerivAt_deriv_e8Q hy hθ2
  have hθ2eq : deriv (deriv e8Theta) (e8Q y) = theta2 := hθ2.deriv
  constructor
  · simpa [e8QSecondJet, deriv_e8Q hy] using hq1
  · simpa [e8QSecondJet, hθ2eq] using hq2

/-- The concrete second derivative recovered from the sound jet. -/
theorem deriv2_e8Q_eq_secondJet {y theta2 : ℝ} (hy : y ∈ e8SlopeRange)
    (hθ2 : HasDerivAt (deriv e8Theta) theta2 (e8Q y)) :
    deriv (deriv e8Q) y = e8QSecondJet.second y := by
  exact (e8QSecondJet_soundAt hy hθ2).2.deriv

/-- The concrete inverse jet through order two, now discharged directly from
the radial-contact formulas. -/
theorem e8QSecondJet_soundAt_unconditional {y : ℝ} (hy : y ∈ e8SlopeRange) :
    e8QSecondJet.SoundAt y := by
  exact e8QSecondJet_soundAt hy
    (GeneralCK.hasDerivAt_deriv_e8Theta (e8Q_pos hy))

/-- Unconditional identification of the concrete second derivative. -/
theorem deriv2_e8Q_eq_secondJet_unconditional {y : ℝ} (hy : y ∈ e8SlopeRange) :
    deriv (deriv e8Q) y = e8QSecondJet.second y :=
  (e8QSecondJet_soundAt_unconditional hy).2.deriv

end GeneralCK.Certificates.E8LineAnchorInverseBridge

end



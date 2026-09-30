-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ComplexLogBoxChecker
-- name    : CK_GeneralCK_Certificates_E8ComplexLogBoxChecker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:35:53.396081+00:00
-- url     : https://prove2.me/theorems/243493fe-f96d-4b7d-8502-f4907881ef03
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ComplexLogBoxChecker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ComplexLogBoxChecker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ComplexLogBoxChecker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ComplexLogBoxChecker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ComplexLogBoxChecker.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8GaussianRatBall

-- ===== source module GeneralCK.Certificates.E8ComplexLogBoxChecker =====
section

/-!
# Executable principal-log boxes for the E8 contact disc

This is the deliberately scoped checker used by the E8 derivative
certificate.  Given one exact rational ball for the contact coordinate, it
computes rational balls for precisely the three logarithms in `thetaParam`.
-/

namespace GeneralCK.Certificates.E8ComplexLogBoxChecker

open E8ComplexBallKernel E8GaussianRatBall

def contactRadiusQ : ℚ := 1103 / 2500
def squareRadiusQ : ℚ := contactRadiusQ ^ 2

structure LogBoxes where
  plus : RatBall
  minus : RatBall
  square : RatBall
  deriving DecidableEq, Repr

/-- Pure rational computation of the three order-12 Taylor boxes. -/
def checkLogs (c : RatBall) : LogBoxes :=
  ⟨c.logOnePlus12 contactRadiusQ,
   c.neg.logOnePlus12 contactRadiusQ,
   (c.pow 2).neg.logOnePlus12 squareRadiusQ⟩

theorem checkLogs_sound {cBall : RatBall} {c : ℂ}
    (hcBall : cBall.Holds c) (hc : ‖c‖ ≤ (contactRadiusQ : ℝ)) :
    (checkLogs cBall).plus.Holds (Complex.log (1 + c)) ∧
    (checkLogs cBall).minus.Holds (Complex.log (1 - c)) ∧
    (checkLogs cBall).square.Holds (Complex.log (1 - c ^ 2)) := by
  have hplus := holds_logOnePlus12 hcBall hc
    (by norm_num [contactRadiusQ])
  have hnegBall := holds_neg hcBall
  have hminus := holds_logOnePlus12 hnegBall (by simpa using hc)
    (by norm_num [contactRadiusQ])
  have hsqBall := holds_neg (holds_pow hcBall 2)
  have hsqNorm : ‖-(c ^ 2)‖ ≤ (squareRadiusQ : ℝ) := by
    rw [norm_neg, norm_pow]
    have h := pow_le_pow_left₀ (norm_nonneg c) hc 2
    simpa [squareRadiusQ] using h
  have hsquare := holds_logOnePlus12 hsqBall hsqNorm
    (by norm_num [squareRadiusQ, contactRadiusQ])
  simpa [checkLogs, sub_eq_add_neg] using And.intro hplus (And.intro hminus hsquare)

end GeneralCK.Certificates.E8ComplexLogBoxChecker

end



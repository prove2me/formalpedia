-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8QuadraticBallAcceptance
-- name    : CK_GeneralCK_Certificates_E8QuadraticBallAcceptance
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:54:51.835669+00:00
-- url     : https://prove2.me/theorems/d32ab4f4-96cb-472f-b363-5b0e766295f9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8QuadraticBallAcceptance` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8QuadraticBallAcceptance` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8QuadraticBallAcceptance` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8QuadraticBallAcceptance (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8QuadraticBallAcceptance.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8RoundedDerivativeEvaluator

-- ===== source module GeneralCK.Certificates.E8QuadraticBallAcceptance =====
section

/-! A rational squared-Euclidean acceptance test.  This avoids the large loss
of the previous L1 test when the output center is diagonal. -/

namespace GeneralCK.Certificates.E8QuadraticBallAcceptance

open E8ComplexBallKernel E8GaussianRatBall

def acceptsUnitSq (b : RatBall) : Bool :=
  decide (0 ≤ b.radius ∧ b.radius ≤ 1 ∧
    b.center.re ^ 2 + b.center.im ^ 2 ≤ (1 - b.radius) ^ 2)

theorem acceptsUnitSq_sound {b : RatBall} (h : acceptsUnitSq b = true)
    {z : ℂ} (hz : b.Holds z) : ‖z‖ ≤ 1 := by
  have hb : 0 ≤ b.radius ∧ b.radius ≤ 1 ∧
      b.center.re ^ 2 + b.center.im ^ 2 ≤ (1 - b.radius) ^ 2 :=
    of_decide_eq_true h
  have hr0 : (0 : ℝ) ≤ (b.radius : ℝ) := by exact_mod_cast hb.1
  have hr1 : (b.radius : ℝ) ≤ 1 := by exact_mod_cast hb.2.1
  have hsquare : ‖b.center.val‖ ^ 2 ≤ (1 - (b.radius : ℝ)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [val_re, val_im]
    have hq := hb.2.2
    simp only [pow_two] at hq ⊢
    exact_mod_cast hq
  have hcenter : ‖b.center.val‖ ≤ 1 - (b.radius : ℝ) := by nlinarith [norm_nonneg b.center.val]
  unfold RatBall.Holds InBall at hz
  calc
    ‖z‖ ≤ ‖b.center.val‖ + ‖z - b.center.val‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ ‖b.center.val‖ + (b.radius : ℝ) := add_le_add_right hz _
    _ ≤ 1 := by linarith

end GeneralCK.Certificates.E8QuadraticBallAcceptance

end



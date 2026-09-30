-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8ComplexBallKernel
-- name    : CK_GeneralCK_Certificates_E8ComplexBallKernel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:23:18.730973+00:00
-- url     : https://prove2.me/theorems/b75e3fe9-8f3f-4f5f-ac0c-cfb953fc7590
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8ComplexBallKernel` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8ComplexBallKernel` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8ComplexBallKernel` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8ComplexBallKernel (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8ComplexBallKernel.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8ThetaTauDerivativeFormula
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

-- ===== source module GeneralCK.Certificates.E8ComplexBallKernel =====
section

/-!
# Sound complex-ball arithmetic for the E8 inverse certificate

This deliberately small kernel supports the operations occurring in the
explicit `thetaParam` derivative: ring operations, reciprocal, and principal
`log (1+z)` on the unit disc.  Certificate generators may use Gaussian
rational centers and rational radii; all acceptance claims pass through the
theorems below.
-/

namespace GeneralCK.Certificates.E8ComplexBallKernel

open Complex

/-- `z` lies in the closed complex ball with center `c` and radius `r`. -/
def InBall (z c : ℂ) (r : ℝ) : Prop := ‖z - c‖ ≤ r

theorem radius_nonneg {z c : ℂ} {r : ℝ} (h : InBall z c r) : 0 ≤ r :=
  (norm_nonneg _).trans h

theorem center (z : ℂ) : InBall z z 0 := by simp [InBall]

theorem add {x y cx cy : ℂ} {rx ry : ℝ}
    (hx : InBall x cx rx) (hy : InBall y cy ry) :
    InBall (x + y) (cx + cy) (rx + ry) := by
  unfold InBall at *
  have hident : x + y - (cx + cy) = (x - cx) + (y - cy) := by ring
  rw [hident]
  exact (norm_add_le _ _).trans (add_le_add hx hy)

theorem neg {x cx : ℂ} {rx : ℝ} (hx : InBall x cx rx) :
    InBall (-x) (-cx) rx := by
  unfold InBall at *
  rw [show -x - -cx = -(x - cx) by ring, norm_neg]
  exact hx

theorem sub {x y cx cy : ℂ} {rx ry : ℝ}
    (hx : InBall x cx rx) (hy : InBall y cy ry) :
    InBall (x - y) (cx - cy) (rx + ry) := by
  simpa [sub_eq_add_neg] using add hx (neg hy)

/-- Multiplication with supplied rational upper bounds for the center norms.
The output radius is the standard first-order ball product plus `rx*ry`. -/
theorem mul {x y cx cy : ℂ} {rx ry ux uy : ℝ}
    (hx : InBall x cx rx) (hy : InBall y cy ry)
    (hcx : ‖cx‖ ≤ ux) (hcy : ‖cy‖ ≤ uy) :
    InBall (x * y) (cx * cy) (ux * ry + uy * rx + rx * ry) := by
  have hrx := radius_nonneg hx
  have hry := radius_nonneg hy
  have hux : 0 ≤ ux := (norm_nonneg cx).trans hcx
  have huy : 0 ≤ uy := (norm_nonneg cy).trans hcy
  unfold InBall at *
  have hid : x * y - cx * cy = cx * (y - cy) + cy * (x - cx) + (x - cx) * (y - cy) := by
    ring
  rw [hid]
  calc
    ‖cx * (y - cy) + cy * (x - cx) + (x - cx) * (y - cy)‖ ≤
        ‖cx * (y - cy)‖ + ‖cy * (x - cx)‖ + ‖(x - cx) * (y - cy)‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖cx‖ * ‖y - cy‖ + ‖cy‖ * ‖x - cx‖ +
        ‖x - cx‖ * ‖y - cy‖ := by simp only [norm_mul]
    _ ≤ ux * ry + uy * rx + rx * ry := by
      gcongr

/-- A lower norm bound obtained from a center norm lower bound. -/
theorem norm_lower {z c : ℂ} {r lower : ℝ}
    (hz : InBall z c r) (hc : lower ≤ ‖c‖) : lower - r ≤ ‖z‖ := by
  unfold InBall at hz
  have h := norm_sub_norm_le c z
  rw [norm_sub_rev] at h
  nlinarith

/-- Reciprocal ball.  `lower` is any certified lower bound for `‖c‖`.
The hypotheses make both the true value and center nonzero. -/
theorem inv {z c : ℂ} {r lower : ℝ}
    (hz : InBall z c r) (hc : lower ≤ ‖c‖) (hr : r < lower) :
    InBall z⁻¹ c⁻¹ (r / ((lower - r) * lower)) := by
  have hlower : 0 < lower := lt_of_le_of_lt (radius_nonneg hz) hr
  have hznorm : lower - r ≤ ‖z‖ := norm_lower hz hc
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (sub_pos.mpr hr) hznorm
  have hcpos : 0 < ‖c‖ := lt_of_lt_of_le hlower hc
  have hz0 : z ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at hzpos
    exact lt_irrefl 0 hzpos
  have hc0 : c ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at hcpos
    exact lt_irrefl 0 hcpos
  unfold InBall at *
  rw [inv_sub_inv hz0 hc0, norm_div, norm_mul]
  have hden : (lower - r) * lower ≤ ‖z‖ * ‖c‖ :=
    mul_le_mul hznorm hc hlower.le (norm_nonneg _)
  have hz' : ‖c - z‖ ≤ r := by simpa [norm_sub_rev] using hz
  apply (div_le_div_iff₀ (mul_pos hzpos hcpos)
    (mul_pos (sub_pos.mpr hr) hlower)).2
  exact mul_le_mul hz' hden (mul_nonneg (sub_pos.mpr hr).le hlower.le)
    (radius_nonneg hz)

/-- Sound principal-log enclosure around the exact Taylor polynomial. -/
theorem log_one_add_taylor {z : ℂ} {r : ℝ} (n : ℕ)
    (hz : ‖z‖ ≤ r) (hr : r < 1) :
    InBall (Complex.log (1 + z)) (Complex.logTaylor (n + 1) z)
      (r ^ (n + 1) * (1 - r)⁻¹ / (n + 1)) := by
  unfold InBall
  exact (Complex.norm_log_sub_logTaylor_le n (lt_of_le_of_lt hz hr)).trans (by
    have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
    have hInv : (1 - ‖z‖)⁻¹ ≤ (1 - r)⁻¹ := by
      rw [inv_le_inv₀ (sub_pos.mpr (lt_of_le_of_lt hz hr)) (sub_pos.mpr hr)]
      linarith
    have hInv0 : 0 ≤ (1 - ‖z‖)⁻¹ := (inv_nonneg.mpr (by linarith))
    gcongr)

/-- Convenient order-12 specialization used by the E8 generator. -/
theorem log_one_add_taylor12 {z : ℂ} {r : ℝ}
    (hz : ‖z‖ ≤ r) (hr : r < 1) :
    InBall (Complex.log (1 + z)) (Complex.logTaylor 13 z)
      (r ^ 13 * (1 - r)⁻¹ / 13) := by
  convert log_one_add_taylor 12 hz hr using 1 <;> norm_num

end GeneralCK.Certificates.E8ComplexBallKernel

end



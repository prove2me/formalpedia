-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8HalfMean
-- name    : CK_GeneralCK_PureGapE8HalfMean
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T18:55:45.766722+00:00
-- url     : https://prove2.me/theorems/34219953-23e2-45a5-a74e-86153cd676f7
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8HalfMean` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8HalfMean` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8HalfMean` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8HalfMean (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8HalfMean.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8InverseDerivatives

-- ===== source module GeneralCK.PureGapE8HalfMean =====
section

/-!
# Equation (8) on the half-mean axis

This identifies the manuscript's scalar `D₀` with the inward derivative of
the equation-(8) determinant at `t = 0`.  The statement is generic in the
inverse function and keeps the endpoint derivative explicit, so it can be
instantiated once the analytic extension of `e8Q` at zero is available.
-/

namespace GeneralCK

/-- The scalar half-mean certificate expression.  The parameter `q0` is the
derivative of the inverse slope map at zero. -/
noncomputable def e8D0 (Q : ℝ → ℝ) (q0 s : ℝ) : ℝ :=
  deriv Q s * Q (2 * s) - 2 * q0 * (Q (2 * s) - Q s)

/-- Differentiating equation (8) in its second slope variable at the axis
gives exactly the half-mean scalar expression. -/
theorem hasDerivAt_e8Delta_right_zero {Q : ℝ → ℝ} {s q0 qs q2s : ℝ}
    (hQ0 : Q 0 = 0)
    (h0 : HasDerivAt Q q0 0)
    (hs : HasDerivAt Q qs s)
    (h2s : HasDerivAt Q q2s (2 * s)) :
    HasDerivAt (fun t => e8Delta Q s t)
      (qs * Q (2 * s) - 2 * q0 * (Q (2 * s) - Q s)) 0 := by
  have h2st : HasDerivAt (fun t : ℝ => Q (2 * s + t)) q2s 0 := by
    have h2s' : HasDerivAt Q q2s (2 * s + 0) := by simpa using h2s
    exact h2s'.comp_const_add (2 * s) 0
  have hst : HasDerivAt (fun t : ℝ => Q (s + t)) qs 0 := by
    have hs' : HasDerivAt Q qs (s + 0) := by simpa using hs
    exact hs'.comp_const_add s 0
  have hQs : HasDerivAt (fun _ : ℝ => Q s) 0 0 := hasDerivAt_const 0 _
  have hA := h2st.sub hQs
  have hB := hst.sub h0
  have hC := h2st.sub hst
  have hD := hQs.add h0
  have hd := (hA.mul hB).sub (hC.mul hD)
  change HasDerivAt
    (((fun t : ℝ => Q (2 * s + t)) - fun _ => Q s) *
      ((fun t : ℝ => Q (s + t)) - Q) -
      ((fun t : ℝ => Q (2 * s + t)) - fun t => Q (s + t)) *
      ((fun _ : ℝ => Q s) + Q))
    (qs * Q (2 * s) - 2 * q0 * (Q (2 * s) - Q s)) 0
  have hcoef :
      (q2s - 0) * (Q s - Q 0) + (Q (2 * s) - Q s) * (qs - q0) -
          ((q2s - qs) * (Q s + Q 0) + (Q (2 * s) - Q s) * (0 + q0)) =
        qs * Q (2 * s) - 2 * q0 * (Q (2 * s) - Q s) := by
    rw [hQ0]
    ring
  rw [← hcoef]
  simpa only [Pi.sub_apply, Pi.add_apply, add_zero] using hd

theorem deriv_e8Delta_right_zero {Q : ℝ → ℝ} {s q0 qs q2s : ℝ}
    (hQ0 : Q 0 = 0)
    (h0 : HasDerivAt Q q0 0)
    (hs : HasDerivAt Q qs s)
    (h2s : HasDerivAt Q q2s (2 * s)) :
    deriv (fun t => e8Delta Q s t) 0 =
      qs * Q (2 * s) - 2 * q0 * (Q (2 * s) - Q s) :=
  (hasDerivAt_e8Delta_right_zero hQ0 h0 hs h2s).deriv

/-- Version stated using the actual derivative values of `Q`. -/
theorem deriv_e8Delta_right_zero_eq_e8D0 {Q : ℝ → ℝ} {s q0 : ℝ}
    (hQ0 : Q 0 = 0)
    (h0 : HasDerivAt Q q0 0)
    (hs : DifferentiableAt ℝ Q s)
    (h2s : DifferentiableAt ℝ Q (2 * s)) :
    deriv (fun t => e8Delta Q s t) 0 = e8D0 Q q0 s := by
  rw [deriv_e8Delta_right_zero hQ0 h0 hs.hasDerivAt h2s.hasDerivAt]
  rfl

/-- On the positive slope range, the interior derivative in the `D₀`
formula is the concrete inverse derivative proved earlier. -/
theorem e8D0_eq_inverse_formula {s q0 : ℝ} (hs : s ∈ e8SlopeRange) :
    e8D0 e8Q q0 s =
      (deriv e8Theta (e8Q s))⁻¹ * e8Q (2 * s) -
        2 * q0 * (e8Q (2 * s) - e8Q s) := by
  rw [e8D0, deriv_e8Q hs]

/-- The division step in the manuscript's half-mean argument.  Written this
way, all positivity assumptions needed to clear the two denominators are
visible in the statement. -/
theorem halfMean_slope_lt_of_D0_pos {x y theta0 thetaX : ℝ}
    (htheta0 : 0 < theta0) (hthetaX : 0 < thetaX) (hy : 0 < y)
    (hD : 0 < thetaX⁻¹ * y - 2 * theta0⁻¹ * (y - x)) :
    2 * thetaX * (1 - x / y) < theta0 := by
  have hscale : 0 < theta0 * thetaX / y := by positivity
  have hscaled := mul_pos hD hscale
  have hid :
      (thetaX⁻¹ * y - 2 * theta0⁻¹ * (y - x)) *
          (theta0 * thetaX / y) =
        theta0 - 2 * thetaX * (1 - x / y) := by
    field_simp [ne_of_gt htheta0, ne_of_gt hthetaX, ne_of_gt hy]
  rw [hid] at hscaled
  linarith

/-- A positive concrete half-mean scalar gives precisely the strict slope
inequality used in the transverse second-derivative computation. -/
theorem e8D0_pos_implies_halfMean_slope_lt {s q0 theta0 : ℝ}
    (hs : s ∈ e8SlopeRange) (h2s : 2 * s ∈ e8SlopeRange)
    (htheta0 : 0 < theta0) (hq0 : q0 = theta0⁻¹)
    (hD : 0 < e8D0 e8Q q0 s) :
    2 * deriv e8Theta (e8Q s) *
        (1 - e8Q s / e8Q (2 * s)) < theta0 := by
  apply halfMean_slope_lt_of_D0_pos htheta0
    (deriv_e8Theta_pos (e8Q_pos hs)) (e8Q_pos h2s)
  rw [e8D0_eq_inverse_formula hs, hq0] at hD
  exact hD

/-- Multiplying the slope gap by the positive entropy scale preserves its
strict negativity.  This is the final algebraic step in the curvature formula
of the smooth half-mean exclusion. -/
theorem halfMean_transverse_curvature_neg {x y theta0 thetaX f : ℝ}
    (hf : 0 < f) (hgap : 2 * thetaX * (1 - x / y) < theta0) :
    (1 / f) * (2 * thetaX * (1 - x / y) - theta0) < 0 := by
  exact mul_neg_of_pos_of_neg (one_div_pos.mpr hf) (sub_neg.mpr hgap)

/-- At a right half-mean point, stationarity in the other mean is exactly the
scalar relation `Theta(y) = 2 Theta(x)` used in Appendix R.3. -/
theorem halfMean_left_stationarity_to_e8Theta {a e f : ℝ}
    (ha : a < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hstationary :
      -deriv (fun r => F r ((e + f) / 2)) (1 / 2 - a) -
          deriv (fun r => F r ((e + f) / 2)) (1 - a - 1 / 2) +
          deriv (fun r => F r e) (1 - 2 * a) = 0) :
    e8Theta ((1 / 2 - a) / e) =
      2 * e8Theta ((1 / 2 - a) / (e + f)) := by
  have hv : 0 < 1 / 2 - a := by linarith
  have hv' : 0 < 1 - a - 1 / 2 := by linarith
  have h2v : 0 < 1 - 2 * a := by linarith
  have hef : 0 < (e + f) / 2 := by linarith
  rw [deriv_F_radius_eq_e8Theta hv hef,
    deriv_F_radius_eq_e8Theta hv' hef,
    deriv_F_radius_eq_e8Theta h2v he] at hstationary
  have hcenter1 : (1 / 2 - a) / (2 * ((e + f) / 2)) =
      (1 / 2 - a) / (e + f) := by
    field_simp [show e + f ≠ 0 by linarith]
  have hcenter2 : (1 - a - 1 / 2) / (2 * ((e + f) / 2)) =
      (1 / 2 - a) / (e + f) := by
    field_simp [show e + f ≠ 0 by linarith]
    <;> ring
  have hmarginal : (1 - 2 * a) / (2 * e) = (1 / 2 - a) / e := by
    field_simp [ne_of_gt he]
  rw [hcenter1, hcenter2, hmarginal] at hstationary
  linarith

/-- The concrete inverse sends the two slopes at a stationary half-mean point
back to the manuscript's normalized coordinates. -/
theorem halfMean_stationarity_e8Q_coordinates {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hstationary : e8Theta y = 2 * e8Theta x) :
    e8Q (e8Theta x) = x ∧ e8Q (2 * e8Theta x) = y := by
  constructor
  · exact e8Q_e8Theta hx
  · rw [← hstationary]
    exact e8Q_e8Theta hy

/-- A genuine local minimum at the right half-mean face satisfies the scalar
stationarity relation.  The constrained-to-local reflection step used by the
retained mean set is kept separate from this calculus statement. -/
theorem canonicalPureGap_halfMean_localMin_stationarity {a e f : ℝ}
    (ha : a < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hmin : IsLocalMin
      (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f) (a, 1 / 2)) :
    e8Theta ((1 / 2 - a) / e) =
      2 * e8Theta ((1 / 2 - a) / (e + f)) := by
  apply halfMean_left_stationarity_to_e8Theta ha he hf
  exact canonicalPureGap_left_stationarity ha (by linarith) ha he hf hmin

/-- The complete algebraic use of the scalar `D₀` certificate at a stationary
right half-mean point.  What remains for the analytic certificate is exactly
the global `hD0` hypothesis and the endpoint inverse-derivative identity. -/
theorem canonicalPureGap_halfMean_localMin_slope_lt {a e f q0 theta0 : ℝ}
    (ha : a < 1 / 2) (he : 0 < e) (hf : 0 < f)
    (hmin : IsLocalMin
      (fun q : ℝ × ℝ => canonicalPureGap q.1 q.2 e f) (a, 1 / 2))
    (htheta0 : 0 < theta0) (hq0 : q0 = theta0⁻¹)
    (hD0 : ∀ s : ℝ, 0 < s → 0 < e8D0 e8Q q0 s) :
    2 * deriv e8Theta (e8Q (e8Theta ((1 / 2 - a) / (e + f)))) *
        (1 - e8Q (e8Theta ((1 / 2 - a) / (e + f))) /
          e8Q (2 * e8Theta ((1 / 2 - a) / (e + f)))) < theta0 := by
  let x : ℝ := (1 / 2 - a) / (e + f)
  let y : ℝ := (1 / 2 - a) / e
  let s : ℝ := e8Theta x
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hspos : 0 < s := e8Theta_pos hx
  have hstationary : e8Theta y = 2 * s := by
    dsimp [y, s, x]
    exact canonicalPureGap_halfMean_localMin_stationarity ha he hf hmin
  have hs : s ∈ e8SlopeRange := ⟨x, hx, rfl⟩
  have h2s : 2 * s ∈ e8SlopeRange := ⟨y, hy, hstationary⟩
  exact e8D0_pos_implies_halfMean_slope_lt hs h2s htheta0 hq0 (hD0 s hspos)

end GeneralCK

end



-- Prove2me | Definitions.Def_CK_CKLaneE_KappaFloor
-- name    : CK_CKLaneE_KappaFloor
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:09:51.298805+00:00
-- url     : https://prove2.me/theorems/d904187a-0c91-4d54-92f8-4d442ededce3
-- title:
--   Courtade–Kumar proof module `CKLaneE.KappaFloor` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneE.KappaFloor` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneE.KappaFloor` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneE.KappaFloor (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneE/KappaFloor.lean)

import Definitions.Def_CK_CKLaneE_CertLSR
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

-- ===== source module CKLaneE.KappaFloor =====
section

/-!
# Lane E: a sharper log-sum cost floor (`θ`-enhanced)

The corpus floor `LogSum.cost_lower_bound` uses `bernD u a ≤ χ²(u,a)/log 2` (from `log x ≤ x - 1`).
Using `log x ≤ (x - 1/x)/2` for `x ≥ 1` (i.e. `s ≤ sinh s`) on the term with ratio `≥ 1` gives

  `bernD u a ≤ θ(a) · (u-a)² / (log 2 · a (1-a))`,   `θ(a) = max(1+a, 2-a)/2 ∈ [3/4, 1]`,

hence `cost ≥ interiorCost + (a-b)²/(4 V θ) · ((H a - e) + (H b - f))` with `θ = max(θ(a), θ(b))`.
For `a ≤ b ≤ 1/2` this is `cost ≥ j + (b-a)² s / (b (1-a) (2-a))`, i.e. the log-sum coefficient
`β = 1/(2 b (1-a))` improved by the factor `2/(2-a)` (a lower bound of the archive's `κ(a)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneE.KF

open GeneralCK GeneralCK.LogSum

/-- `log x ≤ (x - x⁻¹)/2` for `x ≥ 1` (equivalently `s ≤ sinh s` for `s = log x ≥ 0`). -/
theorem log_le_half_sub_inv {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ (x - x⁻¹) / 2 := by
  have hx0 : 0 < x := by linarith
  have hs : 0 ≤ Real.log x := Real.log_nonneg hx
  have h := Real.self_le_sinh_iff.mpr hs
  rw [Real.sinh_eq, Real.exp_neg, Real.exp_log hx0] at h
  exact h

noncomputable def theta (a : ℝ) : ℝ := max (1 + a) (2 - a) / 2

/-- Sharpened Bernoulli divergence bound. -/
theorem bernD_le_theta {u a : ℝ} (hu : 0 < u ∧ u < 1) (ha : 0 < a ∧ a < 1) :
    bernD u a ≤ theta a * ((u - a) ^ 2 / (Real.log 2 * a * (1 - a))) := by
  have hL := log_two_pos
  have ha1 : 0 < 1 - a := sub_pos.mpr ha.2
  have hu1 : 0 < 1 - u := sub_pos.mpr hu.2
  have hx : 0 < u / a := div_pos hu.1 ha.1
  have hy : 0 < (1 - u) / (1 - a) := div_pos hu1 ha1
  unfold bernD theta
  rw [div_le_iff₀ hL]
  have hden : 0 < a * (1 - a) := mul_pos ha.1 ha1
  rcases le_total a u with hau | hua
  · -- ratio u/a ≥ 1, ratio (1-u)/(1-a) ≤ 1
    have h1 : Real.log (u / a) ≤ (u / a - (u / a)⁻¹) / 2 :=
      log_le_half_sub_inv ((one_le_div ha.1).mpr hau)
    have h2 : Real.log ((1 - u) / (1 - a)) ≤ (1 - u) / (1 - a) - 1 := Real.log_le_sub_one_of_pos hy
    have t1 := mul_le_mul_of_nonneg_left h1 hu.1.le
    have t2 := mul_le_mul_of_nonneg_left h2 hu1.le
    have e : u * ((u / a - (u / a)⁻¹) / 2) + (1 - u) * ((1 - u) / (1 - a) - 1) =
        (1 + a) / 2 * ((u - a) ^ 2 / (a * (1 - a))) := by
      field_simp [ha.1.ne', ha1.ne', hu.1.ne']
      ring
    have hmax : (1 + a) / 2 * ((u - a) ^ 2 / (a * (1 - a))) ≤
        max (1 + a) (2 - a) / 2 * ((u - a) ^ 2 / (a * (1 - a))) := by
      apply mul_le_mul_of_nonneg_right _ (div_nonneg (sq_nonneg _) hden.le)
      have := le_max_left (1 + a) (2 - a); linarith
    have e2 : max (1 + a) (2 - a) / 2 * ((u - a) ^ 2 / (Real.log 2 * a * (1 - a))) * Real.log 2 =
        max (1 + a) (2 - a) / 2 * ((u - a) ^ 2 / (a * (1 - a))) := by
      field_simp [hL.ne', ha.1.ne', ha1.ne']
    rw [e2]
    linarith
  · -- ratio u/a ≤ 1, ratio (1-u)/(1-a) ≥ 1
    have h1 : Real.log (u / a) ≤ u / a - 1 := Real.log_le_sub_one_of_pos hx
    have h2 : Real.log ((1 - u) / (1 - a)) ≤ ((1 - u) / (1 - a) - ((1 - u) / (1 - a))⁻¹) / 2 :=
      log_le_half_sub_inv ((one_le_div ha1).mpr (by linarith))
    have t1 := mul_le_mul_of_nonneg_left h1 hu.1.le
    have t2 := mul_le_mul_of_nonneg_left h2 hu1.le
    have e : u * (u / a - 1) + (1 - u) * (((1 - u) / (1 - a) - ((1 - u) / (1 - a))⁻¹) / 2) =
        (2 - a) / 2 * ((u - a) ^ 2 / (a * (1 - a))) := by
      field_simp [ha.1.ne', ha1.ne', hu1.ne']
      ring
    have hmax : (2 - a) / 2 * ((u - a) ^ 2 / (a * (1 - a))) ≤
        max (1 + a) (2 - a) / 2 * ((u - a) ^ 2 / (a * (1 - a))) := by
      apply mul_le_mul_of_nonneg_right _ (div_nonneg (sq_nonneg _) hden.le)
      have := le_max_right (1 + a) (2 - a); linarith
    have e2 : max (1 + a) (2 - a) / 2 * ((u - a) ^ 2 / (Real.log 2 * a * (1 - a))) * Real.log 2 =
        max (1 + a) (2 - a) / 2 * ((u - a) ^ 2 / (a * (1 - a))) := by
      field_simp [hL.ne', ha.1.ne', ha1.ne']
    rw [e2]
    linarith

theorem theta_pos (a : ℝ) (ha : 0 < a ∧ a < 1) : 0 < theta a := by
  unfold theta
  have := le_max_left (1 + a) (2 - a)
  linarith [ha.1]

/-- Pointwise tangent-gap lower bound with the sharpened divergence bound. -/
theorem tangentGap_theta_lower {a b u v θ : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hu : 0 < u ∧ u < 1) (hv : 0 < v ∧ v < 1)
    (hθa : theta a ≤ θ) (hθb : theta b ≤ θ) :
    (a - b) ^ 2 / (4 * V a b * θ) * (bernD u a + bernD v b) ≤ tangentGap a b u v := by
  have hL := log_two_pos
  have hVp := V_pos ha hb
  have hθ : 0 < θ := (theta_pos a ha).trans_le hθa
  have hχa : 0 ≤ (u - a) ^ 2 / (Real.log 2 * a * (1 - a)) :=
    div_nonneg (sq_nonneg _) (mul_pos (mul_pos hL ha.1) (sub_pos.mpr ha.2)).le
  have hχb : 0 ≤ (v - b) ^ 2 / (Real.log 2 * b * (1 - b)) :=
    div_nonneg (sq_nonneg _) (mul_pos (mul_pos hL hb.1) (sub_pos.mpr hb.2)).le
  have hA : bernD u a ≤ θ * ((u - a) ^ 2 / (Real.log 2 * a * (1 - a))) :=
    (bernD_le_theta hu ha).trans (mul_le_mul_of_nonneg_right hθa hχa)
  have hB : bernD v b ≤ θ * ((v - b) ^ 2 / (Real.log 2 * b * (1 - b))) :=
    (bernD_le_theta hv hb).trans (mul_le_mul_of_nonneg_right hθb hχb)
  have hc : 0 ≤ (a - b) ^ 2 / (4 * V a b * θ) := div_nonneg (sq_nonneg _) (by positivity)
  have h := mul_le_mul_of_nonneg_left (add_le_add hA hB) hc
  refine h.trans ?_
  have hvar := tangentGap_variance_lower ha hb hu hv
  have e : (a - b) ^ 2 / (4 * V a b * θ) *
      (θ * ((u - a) ^ 2 / (Real.log 2 * a * (1 - a))) + θ * ((v - b) ^ 2 / (Real.log 2 * b * (1 - b)))) =
      (a - b) ^ 2 / (4 * Real.log 2 * V a b) *
        ((u - a) ^ 2 / (a * (1 - a)) + (v - b) ^ 2 / (b * (1 - b))) := by
    have ha1 := sub_pos.mpr ha.2
    have hb1 := sub_pos.mpr hb.2
    field_simp [hL.ne', hVp.ne', hθ.ne', ha.1.ne', hb.1.ne', ha1.ne', hb1.ne']
  rw [e]
  exact hvar

/-- The `θ`-enhanced global log-sum cost floor. -/
theorem cost_lower_bound_theta {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) {θ : ℝ}
    (hθa : theta μ.a ≤ θ) (hθb : theta μ.b ≤ θ) :
    interiorCost μ.a μ.b + (μ.a - μ.b) ^ 2 / (4 * V μ.a μ.b * θ) *
      ((H μ.a - μ.e) + (H μ.b - μ.f)) ≤ μ.cost := by
  have h := μ.avg_mono (fun i => tangentGap_theta_lower μ.a_interior μ.b_interior
    (μ.left_interior i) (μ.right_interior i) hθa hθb)
  have he : μ.avg (fun i => bernD (μ.left i) μ.a) = H μ.a - μ.e :=
    avg_bernD μ μ.left_interior
  have hf : μ.avg (fun i => bernD (μ.right i) μ.b) = H μ.b - μ.f :=
    avg_bernD μ μ.right_interior
  rw [avg_const_mul, μ.avg_add, he, hf] at h
  have ht : μ.avg (fun i => tangentGap μ.a μ.b (μ.left i) (μ.right i)) =
      μ.cost - interiorCost μ.a μ.b := by
    unfold tangentGap
    rw [μ.avg_sub, μ.avg_sub, μ.avg_sub, μ.avg_const,
      avg_const_mul, avg_const_mul, μ.avg_sub, μ.avg_sub, μ.avg_const, μ.avg_const]
    change μ.cost - interiorCost μ.a μ.b - gradLeft μ.a μ.b * (μ.a - μ.a) -
      gradRight μ.a μ.b * (μ.b - μ.b) = _
    ring
  rw [ht] at h
  linarith

/-- Same-side form: for `a ≤ b ≤ 1/2`, `cost ≥ j + (b-a)² s / (b (1-a) (2-a))`. -/
theorem cost_floor_sameSide {k : ℕ} (μ : InteriorLaw (Fin k)) (hab : μ.a ≤ μ.b) (hb : μ.b ≤ 1 / 2) :
    interiorCost μ.a μ.b + (μ.b - μ.a) ^ 2 * (1 / (μ.b * (1 - μ.a) * (2 - μ.a))) * μ.meanDeficit ≤
      μ.cost := by
  have ha0 := μ.a_interior.1
  have hθa : theta μ.a ≤ (2 - μ.a) / 2 := by
    unfold theta
    rw [max_def]; split_ifs <;> linarith
  have hθb : theta μ.b ≤ (2 - μ.a) / 2 := by
    unfold theta
    rw [max_def]; split_ifs <;> linarith
  have h := cost_lower_bound_theta μ hθa hθb
  have hV : V μ.a μ.b = μ.b * (1 - μ.a) := by
    simp only [V, max_eq_right hab, min_eq_left hab]
  have hs : μ.meanDeficit = ((H μ.a - μ.e) + (H μ.b - μ.f)) / 2 := rfl
  rw [hV] at h
  have hb0 := μ.b_interior.1
  have ha1 : 0 < 1 - μ.a := by linarith [μ.a_interior.2]
  have h2a : 0 < 2 - μ.a := by linarith
  have e : (μ.a - μ.b) ^ 2 / (4 * (μ.b * (1 - μ.a)) * ((2 - μ.a) / 2)) *
      ((H μ.a - μ.e) + (H μ.b - μ.f)) =
      (μ.b - μ.a) ^ 2 * (1 / (μ.b * (1 - μ.a) * (2 - μ.a))) * μ.meanDeficit := by
    rw [hs]
    field_simp [hb0.ne', ha1.ne', h2a.ne']
    ring
  rw [e] at h
  exact h

end CKLaneE.KF

#check @CKLaneE.KF.cost_floor_sameSide
#print axioms CKLaneE.KF.cost_floor_sameSide

end



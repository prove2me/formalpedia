-- Prove2me | Definitions.Def_CK_CKLaneM2_SLPlane
-- name    : CK_CKLaneM2_SLPlane
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:59:42.997775+00:00
-- url     : https://prove2.me/theorems/5d898ca3-fd13-4081-8ed7-77ffc87cf0f0
-- title:
--   Courtade–Kumar proof module `CKLaneM2.SLPlane` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM2.SLPlane` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM2.SLPlane` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM2.SLPlane (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM2/SLPlane.lean)

import Definitions.Def_CK_CKLaneD_FleetBase
import Definitions.Def_CK_GeneralCK_LogSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

-- ===== source module CKLaneM2.SLPlane =====
section

/-!
# Lane M2b: the shifted log-sum affine minorant of the cost at an arbitrary anchor

Archive method `shifted_logsum` (CK_GENERAL_COMPLETION `opposite/compact/SHIFTED_LOGSUM.py`,
`FULL_ENTROPY_COVER.bound`): a fixed anchor `(α, β)` gives a *global* affine minorant of the cost,
from the pointwise log-sum remainder theorem, averaged over the law.

* `tangentGap_theta_lower` (pointwise, any anchor): `c · (bernD u α + bernD v β) ≤ tangentGap α β u v`
  with `c = (α-β)² / (4 V θ)`, `θ ≥ θ(α), θ(β)`, `θ(z) = max(1+z, 2-z)/2`.  The proofs of
  `log_le_half_sub_inv`, `bernD_le_theta`, `theta_pos`, `tangentGap_theta_lower` are copied verbatim
  from Lane E (`~/ck_lanes_20260923/E/src/CKLaneE/KappaFloor.lean`, namespace `CKLaneE.KF`), because the
  Lane E import chain is heavy and still being rebuilt; they only use the corpus `GeneralCK.LogSum`.
* `slplane_cost_lower` (NEW, law level, any anchor): averaging the pointwise bound,
  `interiorCost α β + gradLeft α β (a-α) + gradRight α β (b-β) + c((H α + (a-α) J α - e) + (H β + (b-β) J β - f)) ≤ cost`.
* `slplane_expand`: the same affine function in closed form (coefficients of `1, a, b, e+f`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM2

open GeneralCK GeneralCK.LogSum

/-- `log x ≤ (x - x⁻¹)/2` for `x ≥ 1` (copied from `CKLaneE.KF.log_le_half_sub_inv`). -/
theorem log_le_half_sub_inv {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ (x - x⁻¹) / 2 := by
  have hx0 : 0 < x := by linarith
  have hs : 0 ≤ Real.log x := Real.log_nonneg hx
  have h := Real.self_le_sinh_iff.mpr hs
  rw [Real.sinh_eq, Real.exp_neg, Real.exp_log hx0] at h
  exact h

noncomputable def theta (a : ℝ) : ℝ := max (1 + a) (2 - a) / 2

/-- Sharpened Bernoulli divergence bound (copied from `CKLaneE.KF.bernD_le_theta`). -/
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
  · have h1 : Real.log (u / a) ≤ (u / a - (u / a)⁻¹) / 2 :=
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
  · have h1 : Real.log (u / a) ≤ u / a - 1 := Real.log_le_sub_one_of_pos hx
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

/-- Pointwise tangent-gap lower bound (copied from `CKLaneE.KF.tangentGap_theta_lower`). -/
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

/-- Averaged entropy divergence at a FIXED anchor `α` (not the law's mean). -/
theorem avg_bernD_anchor {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i ∧ w i < 1) {α : ℝ} (hα : 0 < α ∧ α < 1) :
    μ.avg (fun i => bernD (w i) α) = H α - μ.avg (fun i => H (w i)) + (μ.avg w - α) * J α := by
  have hfun : (fun i => bernD (w i) α) = (fun i => (H α - H (w i)) + (w i - α) * J α) := by
    funext i
    exact bernD_eq_entropy (hw i) hα
  rw [hfun, μ.avg_add, μ.avg_sub, μ.avg_const, avg_mul_const, μ.avg_sub, μ.avg_const]

/-- NEW: the shifted log-sum plane at an arbitrary anchor `(α, β)`, averaged over the law. -/
theorem slplane_cost_lower {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) {α β θ : ℝ}
    (hα : 0 < α ∧ α < 1) (hβ : 0 < β ∧ β < 1) (hθa : theta α ≤ θ) (hθb : theta β ≤ θ) :
    interiorCost α β + gradLeft α β * (μ.a - α) + gradRight α β * (μ.b - β) +
      (α - β) ^ 2 / (4 * V α β * θ) *
        ((H α + (μ.a - α) * J α - μ.e) + (H β + (μ.b - β) * J β - μ.f)) ≤ μ.cost := by
  have h := μ.avg_mono (fun i => tangentGap_theta_lower hα hβ
    (μ.left_interior i) (μ.right_interior i) hθa hθb)
  rw [avg_const_mul, μ.avg_add, avg_bernD_anchor μ μ.left_interior hα,
    avg_bernD_anchor μ μ.right_interior hβ] at h
  have ht : μ.avg (fun i => tangentGap α β (μ.left i) (μ.right i)) =
      μ.cost - interiorCost α β - gradLeft α β * (μ.a - α) - gradRight α β * (μ.b - β) := by
    unfold tangentGap
    rw [μ.avg_sub, μ.avg_sub, μ.avg_sub, μ.avg_const,
      avg_const_mul, avg_const_mul, μ.avg_sub, μ.avg_sub, μ.avg_const, μ.avg_const]
    rfl
  rw [ht] at h
  have he : μ.avg (fun i => H (μ.left i)) = μ.e := rfl
  have hf : μ.avg (fun i => H (μ.right i)) = μ.f := rfl
  have ha : μ.avg μ.left = μ.a := rfl
  have hb : μ.avg μ.right = μ.b := rfl
  rw [he, hf, ha, hb] at h
  linarith

/-- Closed form of the shifted plane: an affine function of `(a, b, e + f)`. -/
theorem slplane_expand {α β A a b e f : ℝ} (hα : 0 < α ∧ α < 1) (hβ : 0 < β ∧ β < 1) :
    interiorCost α β + gradLeft α β * (a - α) + gradRight α β * (b - β) +
      A * ((H α + (a - α) * J α - e) + (H β + (b - β) * J β - f)) =
    A * (H α - α * J α) + A * (H β - β * J β) -
        (β - α) ^ 2 / (2 * (1 - α) * (1 - β)) * (Real.log 2)⁻¹ +
      (J β / 2 + (A - 1 / 2) * J α + (α - β) / (2 * α * (1 - α)) * (Real.log 2)⁻¹) * a +
      (J α / 2 + (A - 1 / 2) * J β + (β - α) / (2 * β * (1 - β)) * (Real.log 2)⁻¹) * b -
      A * (e + f) := by
  have hL := log_two_pos
  have ha1 : 0 < 1 - α := sub_pos.mpr hα.2
  have hb1 : 0 < 1 - β := sub_pos.mpr hβ.2
  unfold interiorCost gradRight gradLeft
  field_simp [hL.ne', hα.1.ne', hβ.1.ne', ha1.ne', hb1.ne']
  ring

end CKLaneM2

end



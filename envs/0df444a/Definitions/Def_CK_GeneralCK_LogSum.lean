-- Prove2me | Definitions.Def_CK_GeneralCK_LogSum
-- name    : CK_GeneralCK_LogSum
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:26:52.228992+00:00
-- url     : https://prove2.me/theorems/dc080b15-9d63-444c-b6cb-56cb131ff62b
-- title:
--   Courtade–Kumar proof module `GeneralCK.LogSum` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.LogSum` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.LogSum` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.LogSum (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/LogSum.lean)

import Definitions.Def_CK_GeneralCK_FiniteLaw
import Mathlib.Analysis.Calculus.MeanValue

/-! Analytic log-sum ingredients in natural units, then converted to bits. -/
namespace GeneralCK.LogSum
open Set
open scoped BigOperators

noncomputable def massD (x y : ℝ) : ℝ := x * Real.log (x / y) - x + y

theorem massD_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 ≤ massD x y := by
  have hl := Real.log_le_sub_one_of_pos (div_pos hy hx)
  have hm := mul_le_mul_of_nonneg_left hl hx.le
  rw [Real.log_div hy.ne' hx.ne'] at hm
  unfold massD
  rw [Real.log_div hx.ne' hy.ne']
  have he : x * (y / x - 1) = y - x := by field_simp
  rw [he] at hm
  nlinarith

/-- The two-term log-sum inequality, for positive unnormalized masses. -/
theorem massD_add_le {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    massD (x₁ + x₂) (y₁ + y₂) ≤ massD x₁ y₁ + massD x₂ y₂ := by
  have hX : 0 < x₁ + x₂ := by positivity
  have hY : 0 < y₁ + y₂ := by positivity
  have h₁ := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (mul_pos hy₁ hX) (mul_pos hx₁ hY))) hx₁.le
  have h₂ := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (mul_pos hy₂ hX) (mul_pos hx₂ hY))) hx₂.le
  rw [Real.log_div (mul_pos hy₁ hX).ne' (mul_pos hx₁ hY).ne',
    Real.log_mul hy₁.ne' hX.ne', Real.log_mul hx₁.ne' hY.ne'] at h₁
  rw [Real.log_div (mul_pos hy₂ hX).ne' (mul_pos hx₂ hY).ne',
    Real.log_mul hy₂.ne' hX.ne', Real.log_mul hx₂.ne' hY.ne'] at h₂
  have he : x₁ * (y₁ * (x₁ + x₂) / (x₁ * (y₁ + y₂)) - 1) +
      x₂ * (y₂ * (x₁ + x₂) / (x₂ * (y₁ + y₂)) - 1) = 0 := by
    field_simp; ring
  unfold massD
  rw [Real.log_div hX.ne' hY.ne', Real.log_div hx₁.ne' hy₁.ne',
    Real.log_div hx₂.ne' hy₂.ne']
  nlinarith

theorem massD_scale {x y c : ℝ} (hc : 0 < c) :
    massD (c * x) (c * y) = c * massD x y := by
  unfold massD
  rw [mul_div_mul_left _ _ hc.ne']; ring

/-- A quantitative scalar log bound with the exact denominator used by the manuscript. -/
theorem log_quadratic {x : ℝ} (hx : 0 < x) :
    (x - 1) ^ 2 / (2 * max 1 x) ≤ x - 1 - Real.log x := by
  by_cases hx1 : 1 ≤ x
  · let g : ℝ → ℝ := fun t => t - 1 - Real.log t - (t - 1) ^ 2 / (2 * t)
    have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt g ((t - 1) ^ 2 / (2 * t ^ 2)) t := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht
      have h := (((hasDerivAt_id t).sub_const 1).sub (Real.hasDerivAt_log ht0)).sub
        ((((hasDerivAt_id t).sub_const 1).pow 2).div ((hasDerivAt_id t).const_mul 2)
          (by positivity : (2 : ℝ) * t ≠ 0))
      convert! h using 1
      dsimp only [id_eq, Pi.pow_apply]
      field_simp
      ring
    have hm : MonotoneOn g (Ioi 0) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (by simpa using ht)).hasDerivWithinAt)
      (fun t _ => by positivity)
    have h := hm (by norm_num : (1 : ℝ) ∈ Ioi 0) hx hx1
    dsimp [g] at h
    rw [max_eq_right hx1]
    norm_num at h
    linarith
  · have hx1' : x ≤ 1 := le_of_not_ge hx1
    let g : ℝ → ℝ := fun t => t - 1 - Real.log t - (t - 1) ^ 2 / 2
    have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt g (-((t - 1) ^ 2 / t)) t := by
      intro t ht
      have ht0 : t ≠ 0 := ne_of_gt ht
      have h := (((hasDerivAt_id t).sub_const 1).sub (Real.hasDerivAt_log ht0)).sub
        ((((hasDerivAt_id t).sub_const 1).pow 2).div_const 2)
      convert! h using 1
      dsimp only [id_eq, Pi.pow_apply]
      field_simp
      ring
    have hm : AntitoneOn g (Ioi 0) := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (by simpa using ht)).hasDerivWithinAt)
      (fun t ht => neg_nonpos.mpr (div_nonneg (sq_nonneg _) (le_of_lt (by simpa using ht))))
    have h := hm hx (by norm_num : (1 : ℝ) ∈ Ioi 0) hx1'
    dsimp [g] at h
    rw [max_eq_left hx1']
    norm_num at h ⊢
    linarith

noncomputable def gradLeft (a b : ℝ) : ℝ :=
  (J b - J a) / 2 + (a - b) / (2 * Real.log 2 * a * (1 - a))
noncomputable def gradRight (a b : ℝ) : ℝ := gradLeft b a
noncomputable def tangentGap (a b u v : ℝ) : ℝ :=
  interiorCost u v - interiorCost a b - gradLeft a b * (u - a) - gradRight a b * (v - b)
noncomputable def row (a b u v : ℝ) : ℝ :=
  massD u (a * v / b) + massD (1 - u) ((1 - a) * (1 - v) / (1 - b))

theorem log_row_ratio {a b u v : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : 0 < u) (hv : 0 < v) :
    Real.log (u / (a * v / b)) = Real.log u - Real.log a - Real.log v + Real.log b := by
  rw [Real.log_div hu.ne' (div_pos (mul_pos ha hv) hb).ne',
    Real.log_div (mul_pos ha hv).ne' hb.ne', Real.log_mul ha.ne' hv.ne']
  ring

/-- Exact Bregman decomposition, before any inequality is applied. -/
theorem tangentGap_eq_rows {a b u v : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hu : 0 < u ∧ u < 1) (hv : 0 < v ∧ v < 1) :
    tangentGap a b u v = (row a b u v + row b a v u) / (2 * Real.log 2) := by
  have ha' : 0 < 1 - a := sub_pos.mpr ha.2
  have hb' : 0 < 1 - b := sub_pos.mpr hb.2
  have hu' : 0 < 1 - u := sub_pos.mpr hu.2
  have hv' : 0 < 1 - v := sub_pos.mpr hv.2
  unfold tangentGap gradRight gradLeft interiorCost J row massD
  rw [log_row_ratio ha.1 hb.1 hu.1 hv.1, log_row_ratio ha' hb' hu' hv',
    log_row_ratio hb.1 ha.1 hv.1 hu.1, log_row_ratio hb' ha' hv' hu',
    Real.log_div ha'.ne' ha.1.ne', Real.log_div hb'.ne' hb.1.ne',
    Real.log_div hu'.ne' hu.1.ne', Real.log_div hv'.ne' hv.1.ne']
  field_simp [ha.1.ne', hb.1.ne', ha'.ne', hb'.ne', log_two_pos.ne']
  ring

theorem row_lower {a b u v : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hu : 0 < u ∧ u < 1) (hv : 0 < v ∧ v < 1) :
    massD 1 (1 + (a - b) * (v - b) / (b * (1 - b))) ≤ row a b u v := by
  have ht₁ : 0 < a * v / b := div_pos (mul_pos ha.1 hv.1) hb.1
  have ht₀ : 0 < (1 - a) * (1 - v) / (1 - b) :=
    div_pos (mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hv.2)) (sub_pos.mpr hb.2)
  have h := massD_add_le hu.1 (sub_pos.mpr hu.2) ht₁ ht₀
  have he : a * v / b + (1 - a) * (1 - v) / (1 - b) =
      1 + (a - b) * (v - b) / (b * (1 - b)) := by
    field_simp [hb.1.ne', (sub_pos.mpr hb.2).ne']; ring
  simpa only [add_sub_cancel, he, row] using h

noncomputable def V (a b : ℝ) : ℝ := max a b * (1 - min a b)

theorem V_comm (a b : ℝ) : V a b = V b a := by simp only [V, max_comm, min_comm]

theorem V_pos {a b : ℝ} (ha : 0 < a ∧ a < 1) (_hb : 0 < b ∧ b < 1) : 0 < V a b := by
  apply mul_pos
  · exact ha.1.trans_le (le_max_left _ _)
  · have h := min_le_left a b; linarith [ha.2]

theorem row_variance_lower {a b u v : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hu : 0 < u ∧ u < 1) (hv : 0 < v ∧ v < 1) :
    (a - b)^2 * (v - b)^2 / (2 * V a b * (b * (1 - b))) ≤ row a b u v := by
  let T := 1 + (a - b) * (v - b) / (b * (1 - b))
  have hn : 0 < b * (1 - b) := mul_pos hb.1 (sub_pos.mpr hb.2)
  have hV := V_pos ha hb
  have hTform : T = a * v / b + (1 - a) * (1 - v) / (1 - b) := by
    dsimp [T]; field_simp [hb.1.ne', (sub_pos.mpr hb.2).ne']; ring
  have hT : 0 < T := by
    rw [hTform]
    exact add_pos (div_pos (mul_pos ha.1 hv.1) hb.1)
      (div_pos (mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hv.2)) (sub_pos.mpr hb.2))
  have hbound : max 1 T ≤ V a b / (b * (1 - b)) := by
    apply max_le
    · apply (le_div_iff₀ hn).2
      by_cases hab : a ≤ b
      · rw [V, max_eq_right hab, min_eq_left hab]; nlinarith
      · rw [V, max_eq_left (le_of_not_ge hab), min_eq_right (le_of_not_ge hab)]
        nlinarith
    · apply (le_div_iff₀ hn).2
      have he : T * (b * (1 - b)) = b * (1 - a) + (a - b) * v := by
        dsimp [T]; field_simp [hn.ne', hb.1.ne', (sub_pos.mpr hb.2).ne']; ring
      rw [he]
      by_cases hab : a ≤ b
      · rw [V, max_eq_right hab, min_eq_left hab]
        nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hab) hv.1.le]
      · have hab' := le_of_not_ge hab
        rw [V, max_eq_left hab', min_eq_right hab']
        nlinarith [mul_le_mul_of_nonneg_left hv.2.le (sub_nonneg.mpr hab')]
  have hmax : 0 < max 1 T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hq : (T - 1)^2 / (2 * (V a b / (b * (1 - b)))) ≤
      (T - 1)^2 / (2 * max 1 T) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  have he : (T - 1)^2 / (2 * (V a b / (b * (1 - b)))) =
      (a - b)^2 * (v - b)^2 / (2 * V a b * (b * (1 - b))) := by
    dsimp [T]; field_simp [hn.ne', hV.ne', hb.1.ne', (sub_pos.mpr hb.2).ne']; ring
  rw [he] at hq
  have hl := log_quadratic hT
  have hr := row_lower ha hb hu hv
  have hm : massD 1 T = T - 1 - Real.log T := by simp [massD]; ring
  change massD 1 T ≤ _ at hr
  rw [hm] at hr
  exact hq.trans (hl.trans hr)

theorem tangentGap_variance_lower {a b u v : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hu : 0 < u ∧ u < 1) (hv : 0 < v ∧ v < 1) :
    (a - b)^2 / (4 * Real.log 2 * V a b) *
      ((u - a)^2 / (a * (1 - a)) + (v - b)^2 / (b * (1 - b))) ≤
      tangentGap a b u v := by
  have h₁ := row_variance_lower ha hb hu hv
  have h₂ := row_variance_lower hb ha hv hu
  rw [V_comm b a, show (b - a)^2 = (a - b)^2 by ring] at h₂
  rw [tangentGap_eq_rows ha hb hu hv]
  apply (le_div_iff₀ (mul_pos (by norm_num) log_two_pos)).2
  have he : ((a - b)^2 / (4 * Real.log 2 * V a b) *
      ((u - a)^2 / (a * (1 - a)) + (v - b)^2 / (b * (1 - b)))) *
      (2 * Real.log 2) =
      (a - b)^2 * (v - b)^2 / (2 * V a b * (b * (1 - b))) +
      (a - b)^2 * (u - a)^2 / (2 * V a b * (a * (1 - a))) := by
    field_simp [log_two_pos.ne', (V_pos ha hb).ne', ha.1.ne', hb.1.ne',
      (sub_pos.mpr ha.2).ne', (sub_pos.mpr hb.2).ne']; ring
  rw [he]; linarith

noncomputable def bernD (u a : ℝ) : ℝ :=
  (u * Real.log (u / a) + (1 - u) * Real.log ((1 - u) / (1 - a))) / Real.log 2

theorem bernD_eq_entropy {u a : ℝ} (hu : 0 < u ∧ u < 1) (ha : 0 < a ∧ a < 1) :
    bernD u a = H a - H u + (u - a) * J a := by
  unfold bernD H Real.binEntropy J
  rw [Real.log_div hu.1.ne' ha.1.ne',
    Real.log_div (sub_pos.mpr hu.2).ne' (sub_pos.mpr ha.2).ne',
    Real.log_div (sub_pos.mpr ha.2).ne' ha.1.ne']
  simp only [Real.log_inv]
  ring

theorem bernD_le_quadratic {u a : ℝ} (hu : 0 < u ∧ u < 1) (ha : 0 < a ∧ a < 1) :
    bernD u a ≤ (u - a)^2 / (Real.log 2 * a * (1 - a)) := by
  have h₁ := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hu.1 ha.1)) hu.1.le
  have h₂ := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (sub_pos.mpr hu.2) (sub_pos.mpr ha.2)))
    (sub_nonneg.mpr hu.2.le)
  have he : u * (u / a - 1) + (1 - u) * ((1 - u) / (1 - a) - 1) =
      (u - a)^2 / (a * (1 - a)) := by
    field_simp [ha.1.ne', (sub_pos.mpr ha.2).ne']; ring
  have h := div_le_div_of_nonneg_right (add_le_add h₁ h₂) log_two_pos.le
  rw [he] at h
  convert! h using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem tangentGap_bernoulli_lower {a b u v : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hu : 0 < u ∧ u < 1) (hv : 0 < v ∧ v < 1) :
    (a - b)^2 / (4 * V a b) * (bernD u a + bernD v b) ≤ tangentGap a b u v := by
  have hc : 0 ≤ (a - b)^2 / (4 * V a b) := div_nonneg (sq_nonneg _) (by
    have := V_pos ha hb; positivity)
  have h := mul_le_mul_of_nonneg_left
    (add_le_add (bernD_le_quadratic hu ha) (bernD_le_quadratic hv hb)) hc
  apply h.trans
  convert! tangentGap_variance_lower ha hb hu hv using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem avg_mul_const {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) (v : ι → ℝ) (c : ℝ) :
    μ.avg (fun i => v i * c) = μ.avg v * c := by
  simp only [InteriorLaw.avg, Finset.sum_mul, mul_assoc]

theorem avg_const_mul {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) (c : ℝ) (v : ι → ℝ) :
    μ.avg (fun i => c * v i) = c * μ.avg v := by
  simp only [mul_comm c, avg_mul_const]

theorem avg_bernD {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) {v : ι → ℝ}
    (hv : ∀ i, 0 < v i ∧ v i < 1) :
    μ.avg (fun i => bernD (v i) (μ.avg v)) = H (μ.avg v) - μ.avg (H ∘ v) := by
  have hm := μ.avg_interior hv
  simp_rw [bernD_eq_entropy (hv _) hm]
  rw [μ.avg_add, μ.avg_sub, μ.avg_const, avg_mul_const, μ.avg_sub, μ.avg_const]
  simp only [sub_self, zero_mul, add_zero, Function.comp_def]

/-- Global log-sum cost improvement for every finite interior law. -/
theorem cost_lower_bound {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) :
    interiorCost μ.a μ.b + (μ.a - μ.b)^2 / (4 * V μ.a μ.b) *
      ((H μ.a - μ.e) + (H μ.b - μ.f)) ≤ μ.cost := by
  have h := μ.avg_mono (fun i => tangentGap_bernoulli_lower μ.a_interior μ.b_interior
    (μ.left_interior i) (μ.right_interior i))
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
  change (μ.a - μ.b)^2 / (4 * V μ.a μ.b) * ((H μ.a - μ.e) + (H μ.b - μ.f)) ≤ _ at h
  linarith

end GeneralCK.LogSum



-- Prove2me | solution 1 for ApproxEquilibriumCost.General.Supplement.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:11:34.3784+00:00
-- url     : https://prove2.me/submissions/b2b677aa-c9f4-4d0b-80d9-2cba7138de9f

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_Supplement_UpperParameters

section
set_option autoImplicit false

namespace ApproxEquilibriumCost.Dev.A1

open ApproxEquilibriumCost.General.Supplement

lemma lam_eq (d : ℕ) (x : ℝ) :
    lambda d x = x / (1 + x) * (1 - (1 + x) ^ (-(1 / (d : ℝ)))) := by
  unfold lambda
  rw [neg_div]
  rfl

lemma q_nonneg (e z : ℝ) (he : e ≤ 0) (hz : 1 ≤ z) : z ^ e ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hz he

lemma q_anti (e z w : ℝ) (he : e ≤ 0) (hz : 1 ≤ z) (hzw : z ≤ w) : w ^ e ≤ z ^ e :=
  Real.rpow_le_rpow_of_nonpos (by linarith) hzw he

end ApproxEquilibriumCost.Dev.A1

namespace ApproxEquilibriumCost.General.Supplement

theorem chk_lemma_A_1 (d : ℕ) (hd : 1 ≤ d) :
    ContinuousOn (lambda d) (Set.Ici 0) ∧
    StrictMonoOn (lambda d) (Set.Ici 0) ∧
    (lambda d) '' Set.Ici 0 = Set.Ico 0 1 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set e : ℝ := -(1 / (d : ℝ)) with he_def
  have he : e < 0 := by rw [he_def]; have : 0 < 1 / (d:ℝ) := by positivity
                        linarith
  have hlam : ∀ x, lambda d x = x / (1 + x) * (1 - (1 + x) ^ e) :=
    fun x => ApproxEquilibriumCost.Dev.A1.lam_eq d x
  have hcont : ContinuousOn (lambda d) (Set.Ici 0) := by
    have h1 : ContinuousOn (fun x : ℝ => (1 + x) ^ e) (Set.Ici 0) := by
      apply ContinuousOn.rpow_const (by fun_prop)
      intro x hx; left; have : (0:ℝ) ≤ x := hx; linarith
    have h2 : ContinuousOn (fun x : ℝ => x / (1 + x)) (Set.Ici 0) := by
      apply ContinuousOn.div continuousOn_id (by fun_prop)
      intro x hx; have : (0:ℝ) ≤ x := hx; show (1:ℝ) + x ≠ 0; linarith
    have := h2.mul ((continuousOn_const (c := (1:ℝ))).sub h1)
    convert this using 1
    funext x; exact hlam x
  have hnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ lambda d x := by
    intro x hx
    rw [hlam]
    have := ApproxEquilibriumCost.Dev.A1.q_nonneg e (1 + x) he.le (by linarith)
    apply mul_nonneg (div_nonneg hx (by linarith)) (by linarith)
  have hsm : StrictMonoOn (lambda d) (Set.Ici 0) := by
    intro x hx y hy hxy
    have hx0 : (0:ℝ) ≤ x := hx
    have hy0 : (0:ℝ) ≤ y := hy
    rw [hlam, hlam]
    have hp : x / (1 + x) < y / (1 + y) := by
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
    have hq : (1 + y) ^ e ≤ (1 + x) ^ e :=
      ApproxEquilibriumCost.Dev.A1.q_anti e _ _ he.le (by linarith) (by linarith)
    have hq2 : (1 + y) ^ e < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith) he
    have hpx : 0 ≤ x / (1 + x) := div_nonneg hx0 (by linarith)
    calc x / (1 + x) * (1 - (1 + x) ^ e) ≤ x / (1 + x) * (1 - (1 + y) ^ e) :=
          mul_le_mul_of_nonneg_left (by linarith) hpx
      _ < y / (1 + y) * (1 - (1 + y) ^ e) :=
          mul_lt_mul_of_pos_right hp (by linarith)
  have hl0 : lambda d 0 = 0 := by simp [hlam]
  have hlim : Filter.Tendsto (lambda d) Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun x : ℝ => x / (1 + x)) Filter.atTop (nhds 1) := by
      have : Filter.Tendsto (fun x : ℝ => 1 - (1 + x)⁻¹) Filter.atTop (nhds (1 - 0)) :=
        tendsto_const_nhds.sub
          (tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_left _ _ Filter.tendsto_id))
      rw [sub_zero] at this
      refine this.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop 0] with x hx
      field_simp
      ring
    have h2 : Filter.Tendsto (fun x : ℝ => (1 + x) ^ e) Filter.atTop (nhds 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 / (d : ℝ)) (by positivity)).comp
        (Filter.tendsto_atTop_add_const_left _ (1:ℝ) Filter.tendsto_id)
      exact this
    have := h1.mul ((tendsto_const_nhds (x := (1:ℝ))).sub h2)
    have e1 : (1:ℝ) * (1 - 0) = 1 := by norm_num
    rw [e1] at this
    refine this.congr ?_
    intro x; exact (hlam x).symm
  refine ⟨hcont, hsm, ?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨hnn x hx, ?_⟩
    rw [hlam]
    have hx0 : (0:ℝ) ≤ x := hx
    have h1 : x / (1 + x) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have h2 : 0 < (1 + x) ^ e := Real.rpow_pos_of_pos (by linarith) _
    have h3 : 0 ≤ x / (1 + x) := div_nonneg hx0 (by linarith)
    nlinarith
  · rintro y ⟨hy0, hy1⟩
    obtain ⟨X, hX, hX0⟩ := ((hlim.eventually (lt_mem_nhds hy1)).and
      (Filter.eventually_ge_atTop 0)).exists
    have hivt := intermediate_value_Icc hX0
      (hcont.mono (Set.Icc_subset_Ici_self))
    obtain ⟨x, hx, hxy⟩ := hivt ⟨by rw [hl0]; exact hy0, hX.le⟩
    exact ⟨x, hx.1, hxy⟩

end ApproxEquilibriumCost.General.Supplement
end

theorem solution : type_of% @ApproxEquilibriumCost.General.Supplement.chk_lemma_A_1 := @ApproxEquilibriumCost.General.Supplement.chk_lemma_A_1

-- Prove2me | solution 1 for AdaptiveEM.Infinite.eq_47
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:46:14.810741+00:00
-- url     : https://prove2.me/submissions/5e67d8af-a85b-44f7-ad7d-cbab24631940

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Scheme
import Definitions.Def_AdaptiveEM_Infinite_Assumptions

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

open EthierKurtz SabanisEuler.Shared

namespace Aux_AdaptiveEM_eq_47

theorem mulVec_norm_sq_le {m d : ℕ} (A : Diffusion m d) (w : SDEState d) :
    ‖AdaptiveEM.Finite.mulVec A w‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖w‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [AdaptiveEM.Finite.mulVec, PiLp.toLp_apply]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

end Aux_AdaptiveEM_eq_47

open AdaptiveEM.Infinite in
theorem solution {m d : ℕ} {Ω : Type*}
    (f : SDEState m → SDEState m) (g : SDEState m → Diffusion m d) (h : SDEState m → ℝ)
    (x0 : SDEState m) (W : ℝ≥0 → Ω → SDEState d) (hmax α β : ℝ)
    (hA8 : Assumption8 f h hmax α β) (h18 : ∀ x : SDEState m, ‖g x‖ ^ 2 ≤ β)
    (t : ℝ≥0) (ω : Ω) (hreach : ∃ n : ℕ, t < (AdaptiveEM.Finite.grid f g h x0 W (n + 1) ω).1) :
    Real.exp (2 * α * (t : ℝ)) * ‖AdaptiveEM.Finite.Xhat f g h x0 W t ω‖ ^ 2
      ≤ Real.exp (2 * α * (AdaptiveEM.Finite.tlow f g h x0 W t ω : ℝ)) * ‖AdaptiveEM.Finite.Xbar f g h x0 W t ω‖ ^ 2
        + 2 * Real.exp (2 * α * ((AdaptiveEM.Finite.tlow f g h x0 W t ω : ℝ) + hmax)) * β
            * ((t : ℝ) - AdaptiveEM.Finite.tlow f g h x0 W t ω)
        + Real.exp (2 * α * ((AdaptiveEM.Finite.tlow f g h x0 W t ω : ℝ) + hmax)) * β
            * ‖W t ω - W (AdaptiveEM.Finite.tlow f g h x0 W t ω) ω‖ ^ 2
        + 2 * Real.exp (2 * α * (t : ℝ))
            * inner ℝ (AdaptiveEM.Finite.Xbar f g h x0 W t ω
                + ((t : ℝ) - AdaptiveEM.Finite.tlow f g h x0 W t ω) • f (AdaptiveEM.Finite.Xbar f g h x0 W t ω))
              (AdaptiveEM.Finite.mulVec (g (AdaptiveEM.Finite.Xbar f g h x0 W t ω)) (W t ω - W (AdaptiveEM.Finite.tlow f g h x0 W t ω) ω)) := by
  obtain ⟨hcont, hmax0, hhb, hα, hβ, hdiss⟩ := hA8
  have gen : ∀ k : ℕ, (∀ j < k, ¬ t < (AdaptiveEM.Finite.grid f g h x0 W (j + 1) ω).1) →
      (k = 0 ∨ ∃ j, k = j + 1 ∧ (AdaptiveEM.Finite.grid f g h x0 W (j + 1) ω).1 ≤ t) := by
    intro k hk
    cases k with
    | zero => left; rfl
    | succ j => right; exact ⟨j, rfl, not_lt.mp (hk j (Nat.lt_succ_self j))⟩
  obtain ⟨k, hidx, hlt, hcase⟩ : ∃ k, AdaptiveEM.Finite.idx f g h x0 W t ω = k ∧
      t < (AdaptiveEM.Finite.grid f g h x0 W (k + 1) ω).1 ∧
      (k = 0 ∨ ∃ j, k = j + 1 ∧ (AdaptiveEM.Finite.grid f g h x0 W (j + 1) ω).1 ≤ t) := by
    refine ⟨_, rfl, ?_, ?_⟩
    · unfold AdaptiveEM.Finite.idx
      rw [dif_pos hreach]
      exact Nat.find_spec hreach
    · unfold AdaptiveEM.Finite.idx
      rw [dif_pos hreach]
      exact gen _ (fun j hj => Nat.find_min hreach hj)
  have htlow : AdaptiveEM.Finite.tlow f g h x0 W t ω = (AdaptiveEM.Finite.grid f g h x0 W k ω).1 := by
    unfold AdaptiveEM.Finite.tlow; rw [hidx]
  have hXbar : AdaptiveEM.Finite.Xbar f g h x0 W t ω = (AdaptiveEM.Finite.grid f g h x0 W k ω).2 := by
    unfold AdaptiveEM.Finite.Xbar; rw [hidx]
  have hle : (AdaptiveEM.Finite.grid f g h x0 W k ω).1 ≤ t := by
    rcases hcase with h0 | ⟨j, rfl, hj⟩
    · subst h0
      show (0 : ℝ≥0) ≤ t
      exact zero_le
    · exact hj
  have hg : (AdaptiveEM.Finite.grid f g h x0 W (k + 1) ω).1 =
      (AdaptiveEM.Finite.grid f g h x0 W k ω).1 + (h (AdaptiveEM.Finite.grid f g h x0 W k ω).2).toNNReal := rfl
  rw [hg] at hlt
  unfold AdaptiveEM.Finite.Xhat
  rw [htlow, hXbar]
  generalize AdaptiveEM.Finite.grid f g h x0 W k ω = q at hle hlt ⊢
  obtain ⟨T0, x⟩ := q
  dsimp only at hle hlt ⊢
  obtain ⟨hx0, hxmax⟩ := hhb x
  have hle' : (T0 : ℝ) ≤ t := hle
  have hlt' : (t : ℝ) < T0 + h x := by
    have := NNReal.coe_lt_coe.mpr hlt
    rwa [NNReal.coe_add, Real.coe_toNNReal _ hx0.le] at this
  obtain ⟨s, hs⟩ : ∃ s, s = (t : ℝ) - T0 := ⟨_, rfl⟩
  have ht : (t : ℝ) = T0 + s := by linarith
  rw [← hs, ht]
  have hs0 : 0 ≤ s := by linarith
  have hsh : s ≤ h x := by linarith
  set ΔW := W t ω - W T0 ω with hΔW
  set G := AdaptiveEM.Finite.mulVec (g x) ΔW with hG
  set φ := x + s • f x with hφ
  have hGb : ‖G‖ ^ 2 ≤ β * ‖ΔW‖ ^ 2 := by
    have := Aux_AdaptiveEM_eq_47.mulVec_norm_sq_le (g x) ΔW
    have h2 := h18 x
    nlinarith [sq_nonneg ‖ΔW‖]
  have hφb : ‖φ‖ ^ 2 ≤ (1 - 2 * α * s) * ‖x‖ ^ 2 + 2 * s * β := by
    have e : ‖φ‖ ^ 2 = ‖x‖ ^ 2 + 2 * s * (inner ℝ x (f x) + 1 / 2 * s * ‖f x‖ ^ 2) := by
      rw [hφ, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [e]
    have := hdiss x
    have hf2 : 0 ≤ ‖f x‖ ^ 2 := sq_nonneg _
    have : 1 / 2 * s * ‖f x‖ ^ 2 ≤ 1 / 2 * h x * ‖f x‖ ^ 2 := by nlinarith
    nlinarith
  have hsplit : ‖φ + G‖ ^ 2 = ‖φ‖ ^ 2 + 2 * inner ℝ φ G + ‖G‖ ^ 2 := norm_add_sq_real φ G
  rw [hsplit]
  set E := Real.exp (2 * α * (T0 : ℝ)) with hE
  set E' := Real.exp (2 * α * ((T0 : ℝ) + s)) with hE'
  set Em := Real.exp (2 * α * ((T0 : ℝ) + hmax)) with hEm
  have hE'E : E' = E * Real.exp (2 * α * s) := by
    rw [hE', hE, ← Real.exp_add]; ring_nf
  have hkey : Real.exp (2 * α * s) * (1 - 2 * α * s) ≤ 1 := by
    have h1 := Real.add_one_le_exp (-(2 * α * s))
    have h2 : Real.exp (2 * α * s) * Real.exp (-(2 * α * s)) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos (2 * α * s)
    nlinarith
  have hE'Em : E' ≤ Em := by
    rw [hE', hEm]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hEpos : 0 < E := Real.exp_pos _
  have hE'pos : 0 < E' := Real.exp_pos _
  have hx2 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  have hW2 : 0 ≤ ‖ΔW‖ ^ 2 := sq_nonneg _
  have t1 : E' * ((1 - 2 * α * s) * ‖x‖ ^ 2) ≤ E * ‖x‖ ^ 2 := by
    rw [hE'E]
    have : E * Real.exp (2 * α * s) * ((1 - 2 * α * s) * ‖x‖ ^ 2) =
        E * ‖x‖ ^ 2 * (Real.exp (2 * α * s) * (1 - 2 * α * s)) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hkey (mul_nonneg hEpos.le hx2)
    linarith
  have t2 : E' * (2 * s * β) ≤ 2 * Em * β * s := by
    have := mul_le_mul_of_nonneg_right hE'Em (by positivity : (0:ℝ) ≤ 2 * s * β)
    linarith
  have t3 : E' * ‖G‖ ^ 2 ≤ Em * β * ‖ΔW‖ ^ 2 := by
    have a1 := mul_le_mul_of_nonneg_left hGb hE'pos.le
    have a2 := mul_le_mul_of_nonneg_right hE'Em (by positivity : (0:ℝ) ≤ β * ‖ΔW‖ ^ 2)
    linear_combination a1 + a2
  have t0 := mul_le_mul_of_nonneg_left hφb hE'pos.le
  linear_combination t0 + t1 + t2 + t3

-- Prove2me | solution 1 for ApproachRegret.ToOLO.theorem16_regret_le
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T14:06:32.601983+00:00
-- url     : https://prove2.me/submissions/2c3188f1-4401-4f78-bfcd-c6887882ec8d

import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
import Theorems.Thm_ApproachRegret_ToOLO_display8_distance

open scoped RealInnerProductSpace
set_option autoImplicit false

namespace Theorem16Internal

open scoped RealInnerProductSpace
open Set
set_option autoImplicit false

namespace LiftAlgebra
open ApproachRegret.ToOLO

@[simp] lemma lift_zero {d : ℕ} (a : ℝ) (x : E d) : lift a x 0 = a := by
  simp [lift]

@[simp] lemma lift_succ {d : ℕ} (a : ℝ) (x : E d) (i : Fin d) :
    lift a x i.succ = x i := by
  simp [lift]

lemma inner_lift {d : ℕ} (a b : ℝ) (x y : E d) :
    ⟪lift a x, lift b y⟫ = a*b + ⟪x,y⟫ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

lemma norm_lift_sq {d : ℕ} (a : ℝ) (x : E d) :
    ‖lift a x‖ ^ 2 = a^2 + ‖x‖^2 := by
  rw [← real_inner_self_eq_norm_sq, inner_lift, real_inner_self_eq_norm_sq]
  ring

lemma payoff_inner {d : ℕ} (K : Set (E d)) (hk : 0 < kappa K) (x y f : E d) :
    ⟪payoff K x f, lift (kappa K) y⟫ = ⟪f,x⟫ - ⟪f,y⟫ := by
  rw [payoff, inner_lift, inner_neg_left, div_mul_cancel₀ _ (ne_of_gt hk)]
  rfl

lemma norm_le_kappa {d : ℕ} (K : Set (E d)) (hK : IsCompact K) {x : E d}
    (hx : x ∈ K) : ‖x‖ ≤ kappa K := by
  exact le_csSup (hK.image continuous_norm).bddAbove (mem_image_of_mem _ hx)

lemma norm_lift_bound {d : ℕ} (K : Set (E d)) (hK : IsCompact K)
    (hk : 0 < kappa K) {x : E d} (hx : x ∈ K) :
    ‖lift (kappa K) x‖ ≤ 2 * kappa K := by
  have hn := norm_lift_sq (kappa K) x
  have hb := norm_le_kappa K hK hx
  nlinarith [norm_nonneg (lift (kappa K) x), norm_nonneg x]

end LiftAlgebra


open scoped RealInnerProductSpace
open Set
set_option autoImplicit false

namespace RegretBound
open ApproachRegret.ToOLO LiftAlgebra

theorem regret_bound {d : ℕ} (K : Set (E d)) (hK : IsCompact K)
    (hne : K.Nonempty) (hk : 0 < kappa K)
    (hd : ∀ z : E (d+1), ∀ w ∈ cone (lift (kappa K) '' K) ∩ Metric.closedBall 0 1,
      ⟪z,w⟫ ≤ Metric.infDist z (target K))
    (A : (n : ℕ) → (Fin n → E d) → E d) (f : ℕ → E d) (T : ℕ) :
    regret K A f T / (T : ℝ) ≤ 2 * kappa K * approachRate K A f T := by
  classical
  let loss : E d → ℝ := fun x => ∑ t ∈ Finset.Icc 1 T, ⟪f t,x⟫
  have hcont : Continuous loss := by unfold loss; fun_prop
  obtain ⟨x,hx,hxmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  have hleast : IsLeast (loss '' K) (loss x) := by
    refine ⟨mem_image_of_mem _ hx, ?_⟩
    rintro y ⟨v,hv,rfl⟩
    exact hxmin hv
  have hmin : sInf (loss '' K) = loss x := hleast.csInf_eq
  have htwo : 0 < 2 * kappa K := mul_pos (by norm_num) hk
  let w : E (d+1) := (2 * kappa K)⁻¹ • lift (kappa K) x
  have hwc : w ∈ cone (lift (kappa K) '' K) := by
    exact ⟨(2*kappa K)⁻¹, le_of_lt (inv_pos.mpr htwo),
      lift (kappa K) x, mem_image_of_mem _ hx, rfl⟩
  have hwn : ‖w‖ ≤ 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htwo)]
    have hh := norm_lift_bound K hK hk hx
    calc
      (2*kappa K)⁻¹ * ‖lift (kappa K) x‖ ≤ (2*kappa K)⁻¹ * (2*kappa K) :=
        mul_le_mul_of_nonneg_left hh (le_of_lt (inv_pos.mpr htwo))
      _ = 1 := inv_mul_cancel₀ (ne_of_gt htwo)
  let z : E (d+1) := (T:ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, payoff K (play A f t) (f t)
  have hbound := hd z w ⟨hwc, by simpa using hwn⟩
  have heq : ⟪z,w⟫ = (regret K A f T / (T:ℝ)) / (2*kappa K) := by
    dsimp [z,w]
    rw [inner_smul_right, inner_smul_left, sum_inner]
    simp_rw [payoff_inner K hk]
    rw [Finset.sum_sub_distrib]
    change (2*kappa K)⁻¹ * ((T:ℝ)⁻¹ *
      ((∑ t ∈ Finset.Icc 1 T, ⟪f t,play A f t⟫) - loss x)) = _
    rw [regret]
    change _ = ((∑ t ∈ Finset.Icc 1 T, ⟪f t,play A f t⟫) - sInf (loss '' K)) /
      (T:ℝ) / (2*kappa K)
    rw [hmin]
    ring
  rw [heq] at hbound
  have hh := (div_le_iff₀ htwo).mp hbound
  simpa only [approachRate, z, mul_comm (Metric.infDist _ _) (2*kappa K)] using hh

end RegretBound
end Theorem16Internal

open ApproachRegret.ToOLO

/-- Theorem 16, p. 37: Algorithm 1 converts any approachability algorithm into OLO. -/
theorem solution {d : ℕ} (K : Set (E d))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hk : 0 < kappa K)
    (A : (n : ℕ) → (Fin n → E d) → E d)
    (hA : ∀ n (h : Fin n → E d),
      (∀ i, h i ∈ Metric.closedBall (0 : E d) 1) → A n h ∈ K)
    (f : ℕ → E d) (T : ℕ) (hT : 1 ≤ T)
    (hf : ∀ t, 1 ≤ t → t ≤ T → f t ∈ Metric.closedBall (0 : E d) 1) :
    regret K A f T / (T : ℝ) ≤
      2 * kappa K * approachRate K A f T := by
  apply Theorem16Internal.RegretBound.regret_bound K hK hne hk ?_ A f T
  intro z w hw
  exact (display8_distance K z hK hconv hne hk).2 ⟨w,hw,rfl⟩



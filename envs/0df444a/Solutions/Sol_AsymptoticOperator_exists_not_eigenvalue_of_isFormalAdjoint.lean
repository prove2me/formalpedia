-- Prove2me | solution 1 for AsymptoticOperator.exists_not_eigenvalue_of_isFormalAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T17:36:50.565822+00:00
-- url     : https://prove2.me/submissions/26331340-26b9-4a26-b161-dcf0f1a29b73

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Topology.Bases
import Mathlib.Analysis.Real.Cardinality

/-- A symmetric partially defined operator on a separable real inner product space has a real
number that is not an eigenvalue. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [TopologicalSpace.SeparableSpace E] (A : E →ₗ.[ℝ] E)
    (hA : A.IsFormalAdjoint A) :
    ∃ μ : ℝ, ∀ f : A.domain, A f = μ • (f : E) → (f : E) = 0 := by
  by_contra! h
  choose f hf hne using h
  set u : ℝ → E := fun μ => ‖(f μ : E)‖⁻¹ • (f μ : E) with hu
  have hnorm : ∀ μ, ‖u μ‖ = 1 := fun μ => by
    simp only [hu, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hne μ))
  have horth : ∀ μ ν, μ ≠ ν → inner ℝ (u μ) (u ν) = 0 := by
    intro μ ν hμν
    have h1 := hA (f μ) (f ν)
    rw [hf μ, hf ν, real_inner_smul_left, real_inner_smul_right] at h1
    have h0 : inner ℝ (f μ : E) (f ν : E) = 0 := by
      have : (μ - ν) * inner ℝ (f μ : E) (f ν : E) = 0 := by rw [sub_mul, h1, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hμν)
    simp only [hu, real_inner_smul_left, real_inner_smul_right, h0, mul_zero]
  have hdist : ∀ μ ν, μ ≠ ν → 1 < ‖u μ - u ν‖ := by
    intro μ ν hμν
    have h2 : ‖u μ - u ν‖ ^ 2 = 2 := by
      rw [@norm_sub_sq_real, hnorm, hnorm, horth μ ν hμν]; norm_num
    nlinarith [norm_nonneg (u μ - u ν)]
  have hc : Countable ℝ := by
    refine Pairwise.countable_of_isOpen_disjoint (s := fun μ => Metric.ball (u μ) (1 / 2))
      ?_ (fun _ => Metric.isOpen_ball) (fun μ => ⟨u μ, Metric.mem_ball_self (by norm_num)⟩)
    intro μ ν hμν
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    have := hdist μ ν hμν
    have h3 : ‖u μ - u ν‖ ≤ dist x (u μ) + dist x (u ν) := by
      rw [← dist_eq_norm]; exact dist_triangle_left _ _ _
    simp only [Metric.mem_ball] at hx hy
    linarith
  exact Cardinal.not_countable_real (Set.countable_univ_iff.mpr hc)

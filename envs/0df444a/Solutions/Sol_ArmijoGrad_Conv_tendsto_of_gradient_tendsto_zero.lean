-- Prove2me | solution 1 for ArmijoGrad.Conv.tendsto_of_gradient_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T12:10:37.063981+00:00
-- url     : https://prove2.me/submissions/936eb689-a580-46cc-af16-65d10109bc67

import Mathlib
import Definitions.Def_ArmijoGrad_Conv_Setting

open Filter Topology

open ArmijoGrad.Conv Filter Topology in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x0 xstar : EuclideanSpace ℝ (Fin n)) (hIV : ConditionIV f x0 xstar) :
    ∀ y : ℕ → EuclideanSpace ℝ (Fin n), (∀ k, y k ∈ levelSet f x0) →
      Tendsto (fun k => ‖gradient f (y k)‖) atTop (𝓝 0) → Tendsto y atTop (𝓝 xstar) := by
  intro y hy hg
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm, hbound⟩ := hIV.2.2 ε hε
  rw [Metric.tendsto_atTop] at hg
  obtain ⟨N, hN⟩ := hg m hm
  refine ⟨N, fun k hk => ?_⟩
  have h1 := hN k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1
  rw [dist_eq_norm]
  by_contra hc
  have := hbound (y k) (hy k) (not_lt.mp hc)
  linarith

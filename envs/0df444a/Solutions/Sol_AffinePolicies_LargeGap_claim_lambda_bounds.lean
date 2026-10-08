-- Prove2me | solution 1 for AffinePolicies.LargeGap.claim_lambda_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:06:51.298529+00:00
-- url     : https://prove2.me/submissions/b8f37b28-c7bb-48d8-8724-51d933dc665b

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting

open AffinePolicies.LargeGap in
theorem solution (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm : 200 < (m : ℝ) ^ δ)
    (x : Fin m → ℝ) (μ θ lam : ℝ)
    (hfeas : AffinePolicies.Simplex.Feasible (A19 m) (B19 m δ) (U19 m δ) x
      (AffinePolicies.Simplex.affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam)))
    (hcost : AffinePolicies.Simplex.CostLE (c19 m) (d19 m) (U19 m δ) x
      (AffinePolicies.Simplex.affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam))
      ((m : ℝ) ^ ((1 : ℝ) / 2 - δ) / 4)) :
    0 ≤ lam ∧ lam ≤ 1 / (m : ℝ) ^ ((1 : ℝ) / 2 + δ) := by
  have h0 : (0 : Fin m → ℝ) ∈ U19 m δ := by
    unfold U19
    apply subset_convexHull
    simp
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp [Real.zero_rpow hδ.ne'] at hm
      linarith
    · exact h
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  obtain ⟨_, hy⟩ := hfeas
  have hz : ∀ i, Matrix.mulVec (fun i j : Fin m => if i = j then θ else μ) 0 i = 0 := by
    intro i; simp [Matrix.mulVec, dotProduct]
  have hlam : 0 ≤ lam := by
    have := (hy 0 h0).1 ⟨0, hmpos⟩
    simpa [AffinePolicies.Simplex.affinePolicy, Matrix.mulVec_zero, hz] using this
  refine ⟨hlam, ?_⟩
  have hc : (m:ℝ) * lam ≤ (m:ℝ)^((1:ℝ)/2 - δ) / 4 := by
    have := hcost 0 h0
    simpa [AffinePolicies.Simplex.affinePolicy, c19, d19, dotProduct, Matrix.mulVec_zero, hz,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  have hA : 0 < (m:ℝ)^((1:ℝ)/2 - δ) := Real.rpow_pos_of_pos hmR _
  have hB : 0 < (m:ℝ)^((1:ℝ)/2 + δ) := Real.rpow_pos_of_pos hmR _
  have hAB : (m:ℝ)^((1:ℝ)/2 + δ) * (m:ℝ)^((1:ℝ)/2 - δ) = m := by
    rw [← Real.rpow_add hmR, show (1:ℝ)/2 + δ + (1/2 - δ) = 1 by ring, Real.rpow_one]
  rw [le_div_iff₀ hB]
  have h2 : lam * (m:ℝ)^((1:ℝ)/2 + δ) * (m:ℝ)^((1:ℝ)/2 - δ) ≤ 1 * (m:ℝ)^((1:ℝ)/2 - δ) := by
    rw [mul_assoc, hAB]
    nlinarith
  exact le_of_mul_le_mul_right h2 hA

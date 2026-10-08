-- Prove2me | solution 1 for AffinePolicies.TwoGap.claim_diag_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T19:46:24.447515+00:00
-- url     : https://prove2.me/submissions/a428b31e-198c-4e45-82b2-9218f4cd91cb

import Mathlib
import Definitions.Def_AffinePolicies_TwoGap_Setting

set_option autoImplicit false

open AffinePolicies.TwoGap in
theorem solution (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm_even : Even m) (hm0 : 0 < m)
    (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (β : ℝ)
    (hfeas : AffinePolicies.Simplex.Feasible (A6 m) (B6 m) (U6 m) x (AffinePolicies.Simplex.affinePolicy P (fun _ => β)))
    (hcost : AffinePolicies.Simplex.CostLE (c6 m) (d6 m) (U6 m) x (AffinePolicies.Simplex.affinePolicy P (fun _ => β)) (2 - δ)) :
    ∀ j, 1 - 2 / Real.sqrt m - 2 / m ≤ P j j := by
  intro j
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  -- membership of 0 and e_j in U6
  have h0mem : (0 : Fin m → ℝ) ∈ U6 m := by
    apply subset_convexHull
    simp
  have hjmem : (Pi.single j (1 : ℝ) : Fin m → ℝ) ∈ U6 m := by
    apply subset_convexHull
    simp
  -- β bounds from b = 0
  obtain ⟨_, hF⟩ := hfeas
  have hβ0 : 0 ≤ β := by
    have := (hF 0 h0mem).1 j
    simpa [AffinePolicies.Simplex.affinePolicy] using this
  have hβc : (m : ℝ) * β ≤ 2 - δ := by
    have := hcost 0 h0mem
    simpa [AffinePolicies.Simplex.affinePolicy, c6, d6, dotProduct, Finset.sum_const,
      Finset.card_univ] using this
  have hβ : β ≤ 2 / m := by
    rw [le_div_iff₀ hmR]; nlinarith
  -- values at e_j
  have hyv : AffinePolicies.Simplex.affinePolicy P (fun _ => β) (Pi.single j 1)
      = fun i => P i j + β := by
    funext i
    simp [AffinePolicies.Simplex.affinePolicy, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hnn : ∀ i, 0 ≤ P i j + β := by
    intro i
    have := (hF _ hjmem).1 i
    rw [hyv] at this; simpa using this
  have hrow := (hF _ hjmem).2 j
  rw [hyv] at hrow
  have hc := hcost _ hjmem
  rw [hyv] at hc
  simp only [c6, d6, A6, Matrix.zero_mulVec, zero_add, Pi.add_apply, Pi.zero_apply,
    zero_dotProduct, Pi.single_eq_same] at hrow hc
  set s : ℝ := 1 / Real.sqrt m with hs
  have hs0 : 0 ≤ s := by positivity
  set S : ℝ := ∑ i, (P i j + β) with hS
  have hSle : S ≤ 2 - δ := by
    simpa [dotProduct, hS, d6] using hc
  have hrow' : 1 ≤ s * S + (1 - s) * (P j j + β) := by
    have : (B6 m).mulVec (fun i => P i j + β) j = s * S + (1 - s) * (P j j + β) := by
      simp only [Matrix.mulVec, dotProduct, B6]
      have : ∀ i, (if j = i then (1 : ℝ) else 1 / Real.sqrt m) * (P i j + β)
          = s * (P i j + β) + (if j = i then (1 - s) * (P i j + β) else 0) := by
        intro i; split_ifs <;> simp [hs] <;> ring
      rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_add_distrib,
        ← Finset.mul_sum, Finset.sum_ite_eq]
      simp [hS]
    rw [this] at hrow; exact hrow
  have h2s : 2 / Real.sqrt m = 2 * s := by rw [hs]; ring
  rw [h2s]
  have := hnn j
  nlinarith [mul_nonneg hs0 this, mul_le_mul_of_nonneg_left hSle hs0, mul_nonneg hs0 hδ.le]

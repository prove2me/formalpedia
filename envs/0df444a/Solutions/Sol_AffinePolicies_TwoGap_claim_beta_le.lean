-- Prove2me | solution 1 for AffinePolicies.TwoGap.claim_beta_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:54:23.790286+00:00
-- url     : https://prove2.me/submissions/d3254d98-8d61-4443-85c5-270561531693

import Mathlib
import Definitions.Def_AffinePolicies_TwoGap_Setting

open AffinePolicies.TwoGap in
theorem solution (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm_even : Even m) (hm0 : 0 < m)
    (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (β : ℝ)
    (hfeas : AffinePolicies.Simplex.Feasible (A6 m) (B6 m) (U6 m) x (AffinePolicies.Simplex.affinePolicy P (fun _ => β)))
    (hcost : AffinePolicies.Simplex.CostLE (c6 m) (d6 m) (U6 m) x (AffinePolicies.Simplex.affinePolicy P (fun _ => β)) (2 - δ)) :
    β ≤ (2 - δ) / m := by
  have h0 : (0 : Fin m → ℝ) ∈ U6 m := by
    unfold U6
    apply subset_convexHull
    simp
  have h := hcost 0 h0
  simp only [AffinePolicies.Simplex.affinePolicy, Matrix.mulVec_zero, zero_add, c6,
    zero_dotProduct] at h
  have hs : d6 m ⬝ᵥ (fun _ => β) = m * β := by
    simp [d6, dotProduct]
  rw [hs] at h
  have hm : (0:ℝ) < m := by exact_mod_cast hm0
  rw [le_div_iff₀ hm]
  linarith

-- Prove2me | solution 1 for AffinePolicies.TwoGap.claim_entry_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:26:45.281987+00:00
-- url     : https://prove2.me/submissions/10b6892b-581c-47ff-90b1-3fa47b4bc722

import Mathlib
import Definitions.Def_AffinePolicies_TwoGap_Setting

open AffinePolicies.TwoGap in
theorem solution (δ : ℝ) (hδ : 0 < δ) (m : ℕ) (hm_even : Even m) (hm0 : 0 < m)
    (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (β : ℝ)
    (hfeas : AffinePolicies.Simplex.Feasible (A6 m) (B6 m) (U6 m) x (AffinePolicies.Simplex.affinePolicy P (fun _ => β)))
    (hcost : AffinePolicies.Simplex.CostLE (c6 m) (d6 m) (U6 m) x (AffinePolicies.Simplex.affinePolicy P (fun _ => β)) (2 - δ)) :
    ∀ i j, -(2 - δ) / m ≤ P i j := by
  intro i j
  have h0 : (0 : Fin m → ℝ) ∈ U6 m := by
    unfold U6
    apply subset_convexHull
    simp
  have hj : (Pi.single j (1 : ℝ) : Fin m → ℝ) ∈ U6 m := by
    unfold U6
    apply subset_convexHull
    left; right
    exact ⟨j, rfl⟩
  have hc := hcost 0 h0
  have hb : m * β ≤ 2 - δ := by
    simp [AffinePolicies.Simplex.affinePolicy, c6, d6, dotProduct] at hc
    linarith
  have hy := (hfeas.2 _ hj).1 i
  have hPij : 0 ≤ P i j + β := by
    simpa [AffinePolicies.Simplex.affinePolicy, Matrix.mulVec_single] using hy
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm0
  rw [neg_div, neg_le, le_div_iff₀ hmpos]
  have h1 : -P i j * (m : ℝ) ≤ β * m := mul_le_mul_of_nonneg_right (by linarith) hmpos.le
  linarith

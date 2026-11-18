-- Prove2me | solution 1 for AffDisp4n.reroute_matrix_invertible
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:32:34.116201+00:00
-- url     : https://prove2.me/submissions/cddb2ecc-b1e4-4a20-8288-ef04d663849d

import Mathlib
namespace AffDisp4n

theorem reroute_matrix_invertible {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) (ZMod 2))
    (hA : IsUnit A.det) (i k : Fin (r + 1)) (hcol : ∀ i' : Fin (r + 1), i' ≠ i → A i' k = 0) :
    IsUnit (A.submatrix i.succAbove k.succAbove).det := by
  have h := Matrix.det_succ_column A k
  rw [Finset.sum_eq_single i (fun b _ hb => by rw [hcol b hb]; ring) (by simp)] at h
  rw [isUnit_iff_ne_zero] at hA ⊢
  intro h0
  rw [h0, mul_zero] at h
  exact hA h

end AffDisp4n

theorem solution {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) (ZMod 2))
    (hA : IsUnit A.det) (i k : Fin (r + 1)) (hcol : ∀ i' : Fin (r + 1), i' ≠ i → A i' k = 0) :
    IsUnit (A.submatrix i.succAbove k.succAbove).det :=
  AffDisp4n.reroute_matrix_invertible A hA i k hcol

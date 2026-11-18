-- Prove2me | solution 1 for AffDisp4n.exchange_matrix_invertible
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:32:33.460093+00:00
-- url     : https://prove2.me/submissions/30667a9a-03d4-4654-87be-0e0007dfe2fb

import Mathlib
namespace AffDisp4n

theorem exchange_matrix_invertible {r : ℕ} (A : Matrix (Fin r) (Fin r) (ZMod 2)) (hA : IsUnit A.det)
    (ν : Fin r → ZMod 2) (j : Fin r) (hj : (A⁻¹.mulVec ν) j = 1) :
    IsUnit (A.updateCol j ν).det := by
  set t := A⁻¹.mulVec ν with ht
  have hν : ν = fun k => ∑ i, t i • A k i := by
    funext k
    have : A.mulVec t = ν := by
      rw [ht, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec]
    rw [← this]
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [hν, Matrix.det_updateCol_sum, hj, one_smul]
  exact hA

end AffDisp4n

theorem solution {r : ℕ} (A : Matrix (Fin r) (Fin r) (ZMod 2)) (hA : IsUnit A.det)
    (ν : Fin r → ZMod 2) (j : Fin r) (hj : (A⁻¹.mulVec ν) j = 1) :
    IsUnit (A.updateCol j ν).det :=
  AffDisp4n.exchange_matrix_invertible A hA ν j hj

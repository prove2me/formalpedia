-- Prove2me | solution 1 for Algebra.lmul_bezoutian_eq_jacobianDet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/7f2b4290-7cff-5dcc-982a-9ff8d4995c1d

import Mathlib
import Theorems.Thm_MvPolynomial_lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_lmul_bezoutian_eq_jacobianDet

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    (R : Type*) [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    (a : Fin m → Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : ∀ i, f i ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] f i =
      ∑ j, a i j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j)) :
    Algebra.TensorProduct.lmul' R
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
          (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Matrix.det (Matrix.of a))) =
      Ideal.Quotient.mk (Ideal.span (Set.range f)) (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i))) := by
  classical

  have hcomm : (Algebra.TensorProduct.lmul' (S := MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) R).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))) =
      (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))).comp (Algebra.TensorProduct.lmul' (S := MvPolynomial (Fin m) R) R) := by
    ext x
    · simp
    · simp
  have h := DFunLike.congr_fun hcomm (Matrix.det (Matrix.of a))
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h
  rw [h, Ideal.Quotient.mkₐ_eq_mk]
  congr 1

  rw [show Algebra.TensorProduct.lmul' (S := MvPolynomial (Fin m) R) R (Matrix.det (Matrix.of a)) =
      ((Algebra.TensorProduct.lmul' (S := MvPolynomial (Fin m) R) R : MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R →ₐ[R] MvPolynomial (Fin m) R) : MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R →+* MvPolynomial (Fin m) R) (Matrix.det (Matrix.of a)) from rfl,
    RingHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  exact MvPolynomial.lmul_eq_pderiv_of_tmul_one_sub_one_tmul_eq_sum_mul R (f i) (a i) (ha i) j

end S_Algebra_lmul_bezoutian_eq_jacobianDet
end P2MW
export P2MW.S_Algebra_lmul_bezoutian_eq_jacobianDet (solution)

-- Prove2me | solution 1 for Algebra.associated_discr_norm_jacobianDet_of_square_presentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/615c1f62-a7ac-515f-aae2-5518a009470a

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Theorems.Thm_Algebra_exists_dual_bijective_mul_and_trace_eq_jacobianDet_mul_of_square_presentation
import Theorems.Thm_Algebra_det_dual_mul_mul_eq_norm_mul_det
import Theorems.Thm_Algebra_isUnit_det_dual_mul_of_bijective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_associated_discr_norm_jacobianDet_of_square_presentation

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {A : Type} [CommRing A] [Algebra R A]
    [Module.Free R A] [Module.Finite R A]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A)
    {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    (e : (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) ≃ₐ[R] A) :
    Associated (Algebra.discr R b) (Algebra.norm R (e (Ideal.Quotient.mk _ (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i)))))) := by
  classical

  haveI : Module.Free R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) := Module.Free.of_equiv e.toLinearEquiv.symm
  haveI : Module.Finite R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) := Module.Finite.equiv e.toLinearEquiv.symm

  obtain ⟨τ, hτbij, htr⟩ :=
    Algebra.exists_dual_bijective_mul_and_trace_eq_jacobianDet_mul_of_square_presentation R f
  set J : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f) :=
    Ideal.Quotient.mk (Ideal.span (Set.range f)) (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i))) with hJ

  let b' : Module.Basis ι R (MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) := b.map e.toLinearEquiv.symm
  have hb' : ∀ i, b' i = e.symm (b i) := fun i => by simp [b']

  have hdisc : Algebra.discr R b = (Matrix.of fun i j => τ (J * b' i * b' j)).det := by
    rw [Algebra.discr_eq_discr_of_algEquiv b e.symm, Algebra.discr_def]
    congr 1
    ext i j
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.of_apply, htr, mul_assoc]
    simp only [Function.comp_apply, hb']

  have hnorm : Algebra.norm R (e J) = Algebra.norm R J := Algebra.norm_eq_of_algEquiv e J
  rw [hdisc, Algebra.det_dual_mul_mul_eq_norm_mul_det R _ b' τ J]
  show Associated (Algebra.norm R J * (Matrix.of fun i j => τ (b' i * b' j)).det) (Algebra.norm R (e _))
  rw [hnorm]
  obtain ⟨u, hu⟩ := Algebra.isUnit_det_dual_mul_of_bijective R _ b' τ hτbij
  rw [← hu]
  exact (associated_mul_unit_right (Algebra.norm R J) u u.isUnit).symm

end S_Algebra_associated_discr_norm_jacobianDet_of_square_presentation
end P2MW
export P2MW.S_Algebra_associated_discr_norm_jacobianDet_of_square_presentation (solution)

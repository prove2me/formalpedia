-- Prove2me | solution 1 for AronszajnRK.Operators.opKernel_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T12:10:45.70171+00:00
-- url     : https://prove2.me/submissions/4a20e0af-5609-4c7c-9915-5bdfdfc93b7e

import Mathlib
import Definitions.Def_AronszajnRK_Operators_opKernel

open ComplexConjugate

set_option autoImplicit false

open ComplexConjugate AronszajnRK.Operators in
theorem solution {H : Type*} {X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (L : H →L[ℂ] H) (y z : X) :
    opKernel (ContinuousLinearMap.adjoint L) y z = conj (opKernel L z y) := by
  have key : ∀ (x : X) (f : H), f x = inner ℂ (RKHS.kerFun H x (1 : ℂ)) f := by
    intro x f
    rw [RKHS.kerFun_inner]
    simp
  unfold opKernel
  rw [ContinuousLinearMap.adjoint_adjoint, key y, key z, ContinuousLinearMap.adjoint_inner_right,
    inner_conj_symm]

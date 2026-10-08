-- Prove2me | solution 1 for AronszajnRK.Operators.opKernel_comp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:01:49.900982+00:00
-- url     : https://prove2.me/submissions/29f82b68-e619-4a83-85ca-16a5910179a1

import Mathlib
import Definitions.Def_AronszajnRK_Operators_opKernel

open scoped InnerProductSpace
open ComplexConjugate

set_option autoImplicit false

namespace P4e38f038

lemma eval_eq_inner {H : Type*} {X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (f : H) (x : X) :
    f x = ⟪RKHS.kerFun H x (1 : ℂ), f⟫_ℂ := by
  rw [RKHS.kerFun_inner]
  simp

end P4e38f038

open scoped InnerProductSpace in open ComplexConjugate in open AronszajnRK.Operators in
theorem solution {H : Type*} {X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (L₁ L₂ : H →L[ℂ] H) (y z : X) :
    ∃ g₁ g₂ : H, ⇑g₁ = (fun x => opKernel L₁ x z) ∧ ⇑g₂ = (fun x => conj (opKernel L₂ y x)) ∧
      opKernel (L₁ ∘L L₂) y z = ⟪g₂, g₁⟫_ℂ := by
  refine ⟨ContinuousLinearMap.adjoint L₁ (RKHS.kerFun H z (1 : ℂ)),
    L₂ (RKHS.kerFun H y (1 : ℂ)), ?_, ?_, ?_⟩
  · funext x
    rfl
  · funext x
    show (L₂ (RKHS.kerFun H y (1 : ℂ))) x
      = conj ((ContinuousLinearMap.adjoint L₂ (RKHS.kerFun H x (1 : ℂ))) y)
    rw [P4e38f038.eval_eq_inner (ContinuousLinearMap.adjoint L₂ (RKHS.kerFun H x (1 : ℂ))) y,
      ContinuousLinearMap.adjoint_inner_right, inner_conj_symm,
      ← P4e38f038.eval_eq_inner]
  · show (ContinuousLinearMap.adjoint (L₁ ∘L L₂) (RKHS.kerFun H z (1 : ℂ))) y = _
    rw [P4e38f038.eval_eq_inner _ y, ContinuousLinearMap.adjoint_inner_right,
      ContinuousLinearMap.adjoint_inner_right]
    rfl

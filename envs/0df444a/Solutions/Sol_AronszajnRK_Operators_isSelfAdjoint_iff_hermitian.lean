-- Prove2me | solution 1 for AronszajnRK.Operators.isSelfAdjoint_iff_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:50:15.288384+00:00
-- url     : https://prove2.me/submissions/5db6d47d-d137-4e7b-b90f-f0cf6c995e65

import Mathlib
import Definitions.Def_AronszajnRK_Operators_opKernel

set_option autoImplicit false

open ComplexConjugate

theorem p74f_eval_eq_inner {H : Type*} {X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ] (f : H) (x : X) :
    f x = inner ℂ (RKHS.kerFun H x 1) f := by
  rw [RKHS.kerFun_inner]
  simp

theorem p74f_opKernel_eq {H : Type*} {X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ] (L : H →L[ℂ] H) (x y : X) :
    AronszajnRK.Operators.opKernel L x y = conj ((L (RKHS.kerFun H x 1)) y) := by
  unfold AronszajnRK.Operators.opKernel
  rw [p74f_eval_eq_inner, ContinuousLinearMap.adjoint_inner_right, RKHS.inner_kerFun]
  simp

theorem conj_p74f_opKernel_eq {H : Type*} {X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ] (L : H →L[ℂ] H) (x y : X) :
    conj (AronszajnRK.Operators.opKernel L y x) = conj ((ContinuousLinearMap.adjoint L (RKHS.kerFun H x 1)) y) := by
  rfl

open AronszajnRK.Operators ComplexConjugate in
theorem solution {H : Type*} {X : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ] (L : H →L[ℂ] H) :
    IsSelfAdjoint L ↔ ∀ x y : X, opKernel L x y = conj (opKernel L y x) := by
  constructor
  · intro hL x y
    have hA : ContinuousLinearMap.adjoint L = L := hL
    rw [p74f_opKernel_eq, conj_p74f_opKernel_eq, hA]
  · intro h
    have hk : ∀ x : X, L (RKHS.kerFun H x 1) = ContinuousLinearMap.adjoint L (RKHS.kerFun H x 1) := by
      intro x
      apply RKHS.ext
      intro y
      have := h x y
      rw [p74f_opKernel_eq, conj_p74f_opKernel_eq] at this
      simpa using congrArg (starRingEnd ℂ) this
    show ContinuousLinearMap.adjoint L = L
    refine ContinuousLinearMap.ext fun f => RKHS.ext fun y => ?_
    rw [p74f_eval_eq_inner (ContinuousLinearMap.adjoint L f), p74f_eval_eq_inner (L f),
      ← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_adjoint, hk y]

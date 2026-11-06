-- Prove2me | Definitions.Def_TC433_Algebra_DualNumber_Convolution_9113d465b1
-- name    : TC433_Algebra_DualNumber_Convolution_9113d465b1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:20:23.207447+00:00
-- url     : https://prove2.me/theorems/d6b8d9d9-690b-4cdd-87ac-194dd541e826
-- title:
--   TauCeti: Algebra / DualNumber / Convolution
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.DualNumber.Convolution for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/DualNumber/Convolution.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Coalgebra.Convolution
public import Definitions.Def_TC433_Algebra_DualNumber_Basic_8d536c0967

/-!
# Convolution with dual-number coefficients

`WithConv.snd_comp_convMul` computes the first-order coefficient of a convolution
product. This product rule is used to differentiate the adjoint action.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace WithConv

/-- The infinitesimal coefficient of a convolution product of dual-number-valued maps
satisfies the product rule. No counit or coassociativity assumption is needed. -/
theorem snd_comp_convMul
    {R C B : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
    [CoalgebraStruct R C] [Semiring B] [Algebra R B]
    (f g : WithConv (C →ₗ[R] DualNumber B)) :
    (TrivSqZeroExt.sndHom B B).restrictScalars R ∘ₗ (f * g).ofConv =
      (WithConv.toConv ((TrivSqZeroExt.fstHom R B B).toLinearMap ∘ₗ f.ofConv) *
        WithConv.toConv ((TrivSqZeroExt.sndHom B B).restrictScalars R ∘ₗ g.ofConv) +
      WithConv.toConv ((TrivSqZeroExt.sndHom B B).restrictScalars R ∘ₗ f.ofConv) *
        WithConv.toConv ((TrivSqZeroExt.fstHom R B B).toLinearMap ∘ₗ g.ofConv)).ofConv := by
  ext c
  simp [Coalgebra.Repr.convMul_apply (Coalgebra.Repr.arbitrary R c),
    Finset.sum_add_distrib]

end WithConv



-- Prove2me | Definitions.Def_TC433_Compat4331_Tensor_6326550516
-- name    : TC433_Compat4331_Tensor_6326550516
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:09:48.481357+00:00
-- url     : https://prove2.me/theorems/7264d3b2-278f-43db-9359-696daa811549
-- title:
--   TauCeti: Compat4331 / Tensor
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Compat4331.Tensor for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   Compatibility lemma for Mathlib 0df444a360eaa60ab8c11dca51a86af692955474; source and proof included.

module

public import Mathlib.LinearAlgebra.TensorProduct.Defs

@[expose] public section

open scoped TensorProduct

variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

@[elab_as_elim, induction_eliminator]
protected theorem TensorProduct.inductionOn {motive : M ⊗[R] N → Prop}
    (z : M ⊗[R] N) (tmul : ∀ x y, motive (x ⊗ₜ[R] y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add



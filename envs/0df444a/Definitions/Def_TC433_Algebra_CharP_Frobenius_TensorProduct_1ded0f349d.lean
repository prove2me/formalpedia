-- Prove2me | Definitions.Def_TC433_Algebra_CharP_Frobenius_TensorProduct_1ded0f349d
-- name    : TC433_Algebra_CharP_Frobenius_TensorProduct_1ded0f349d
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:14:23.584796+00:00
-- url     : https://prove2.me/theorems/ee8e3e5d-f4c7-41a3-8d80-888b4ea67311
-- title:
--   TauCeti: Algebra / CharP / Frobenius / TensorProduct
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.Algebra.CharP.Frobenius.TensorProduct for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/Algebra/CharP/Frobenius/TensorProduct.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Frobenius on tensor products

The tensor product of Frobenius endomorphisms agrees with Frobenius on the tensor product over a
finite field. This identity makes Frobenius commute with bialgebra comultiplication, allowing the
algebra endomorphism to be promoted to a bialgebra endomorphism.

## References

* Mathlib's `FiniteField.frobeniusAlgHom`, the finite-field Frobenius algebra endomorphism.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace TauCeti

universe u v w

variable (K : Type u) (S : Type v) (T : Type w)
  [Field K] [Fintype K] [CommSemiring S] [CommSemiring T]
  [Algebra K S] [Algebra K T]

/-- The tensor product of the `n`th Frobenius iterates is the `(#K) ^ n`-power map of the tensor
product over the finite field `K`. -/
@[simp]
theorem tensorProductMap_frobeniusAlgHom_pow_apply (n : ℕ) (z : S ⊗[K] T) :
    let : CommRing S := (algebraMap K S).commSemiringToCommRing
    let : CommRing T := (algebraMap K T).commSemiringToCommRing
    Algebra.TensorProduct.map ((FiniteField.frobeniusAlgHom K S) ^ n)
        ((FiniteField.frobeniusAlgHom K T) ^ n) z =
      z ^ (Fintype.card K) ^ n := by
  dsimp only
  let : CommRing S := (algebraMap K S).commSemiringToCommRing
  let : CommRing T := (algebraMap K T).commSemiringToCommRing
  have hmap :
      Algebra.TensorProduct.map ((FiniteField.frobeniusAlgHom K S) ^ n)
          ((FiniteField.frobeniusAlgHom K T) ^ n) =
        (FiniteField.frobeniusAlgHom K (S ⊗[K] T)) ^ n := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_pow,
      FiniteField.coe_frobeniusAlgHom, pow_iterate,
      Algebra.TensorProduct.tmul_pow]
  rw [hmap]
  simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate]

end TauCeti



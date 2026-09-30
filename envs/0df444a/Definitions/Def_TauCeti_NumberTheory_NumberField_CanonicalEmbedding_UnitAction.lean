-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_CanonicalEmbedding_UnitAction
-- name    : TauCeti_NumberTheory_NumberField_CanonicalEmbedding_UnitAction
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:49:25.836648+00:00
-- url     : https://prove2.me/theorems/1353b9c5-a936-4db3-b061-f098b867561e
-- title:
--   The action of units on the mixed space
-- statement:
--   Units of a number field act on its mixed real-complex embedding space by coordinatewise multiplication. The action is commutative and measurable, and is faithful on the mixed images of nonzero field elements. These structures support fundamental-domain and volume arguments.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/CanonicalEmbedding/UnitAction.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/CanonicalEmbedding/UnitAction.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The action of units on the mixed space

This file provides basic compatibility and measurability lemmas for the action of number-field
units on the mixed space.

## Main results

* `TauCeti.NumberField.Units.unitSMul_comm`: two unit actions commute;
* `TauCeti.NumberField.Units.unitSMul_real_smul`: the unit action commutes with real
  scalar multiplication;
* `MeasurableConstSMul (𝓞 K)ˣ (mixedEmbedding.mixedSpace K)`: the action of a fixed unit is
  measurable, so Mathlib's `measurable_const_smul` applies;
* `TauCeti.NumberField.Units.eq_one_of_unitSMul_mixedEmbedding_eq`: a unit fixing the image of a
  nonzero element of `K` is the identity.

It also identifies the units of the mixed space itself:

* `TauCeti.NumberField.mixedEmbedding.isUnit_iff_norm_ne_zero`: a point of the mixed space is a
  unit exactly when its norm is nonzero.
-/

 section

open NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K]

/-- The unit action on the mixed space is commutative: it is multiplication by the mixed embedding
of a unit, and the mixed space is a commutative ring. -/
theorem unitSMul_comm (u v : (𝓞 K)ˣ) (x : mixedEmbedding.mixedSpace K) :
    u • v • x = v • u • x := by
  rw [← mul_smul, ← mul_smul, mul_comm]



/-- The action of a fixed unit on the mixed space is measurable.

Stated as the `MeasurableConstSMul` instance rather than as a bare lemma, because that is what
Mathlib's measure-theoretic API for group actions keys on: `measurable_const_smul` is then the
equation, and `measurePreserving_smul` and the `IsFundamentalDomain` lemmas become available
wherever the action is also measure-preserving. -/
instance [NumberField K] : MeasurableConstSMul (𝓞 K)ˣ (mixedEmbedding.mixedSpace K) :=
  ⟨fun u ↦ by
    simpa only [mixedEmbedding.unitSMul_smul] using
      (continuous_const_mul (mixedEmbedding K (u : K))).measurable⟩

/-- **The unit action on the mixed space is faithful away from zero.**  A unit fixing the image of
a nonzero element of `K` is the identity. -/
theorem eq_one_of_unitSMul_mixedEmbedding_eq [NumberField K] {x : K} (hx : x ≠ 0) {u : (𝓞 K)ˣ}
    (h : u • mixedEmbedding K x = mixedEmbedding K x) : u = 1 := by
  rw [mixedEmbedding.unitSMul_smul, ← map_mul, (mixedEmbedding_injective K).eq_iff,
    mul_eq_right₀ hx] at h
  exact Units.val_eq_one.mp (RingOfIntegers.coe_injective (h.trans (map_one _).symm))

end TauCeti.NumberField.Units

open NumberField.mixedEmbedding

namespace TauCeti.NumberField.mixedEmbedding

variable {K : Type*} [Field K] [NumberField K]



end TauCeti.NumberField.mixedEmbedding

end
end



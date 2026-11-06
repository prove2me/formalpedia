-- Prove2me | Definitions.Def_TC433_RingTheory_Ideal_Cotangent_Basic_8c7f6183b5
-- name    : TC433_RingTheory_Ideal_Cotangent_Basic_8c7f6183b5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:21:40.377195+00:00
-- url     : https://prove2.me/theorems/5e7219a7-f22e-4c59-8354-10b1a316aeb1
-- title:
--   TauCeti: RingTheory / Ideal / Cotangent / Basic
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.RingTheory.Ideal.Cotangent.Basic for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/RingTheory/Ideal/Cotangent/Basic.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Basic

/-!
# Cotangent spaces of augmented algebras

For an augmentation `f : A →ₐ[R] R`, if the augmentation ideal is finitely generated over
`A`, then its cotangent space is finite over `R`.

## Main declarations

* `TauCeti.AlgHom.finite_cotangent_ker_of_fg`: finite generation of the augmentation ideal gives
  finiteness of its cotangent space over the base.
* `TauCeti.AlgHom.finite_cotangent_ker`: the noetherian specialization.

## References

* Mathlib's `Algebra.Extension.Cotangent.finite` provides the generic cotangent-space finiteness
  result used here.
-/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti

namespace AlgHom

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The cotangent space of an augmentation with finitely generated kernel is finite over the
base. -/
theorem finite_cotangent_ker_of_fg (f : A →ₐ[R] R)
    (h : (RingHom.ker f.toRingHom).FG) :
    Module.Finite R (RingHom.ker f.toRingHom).Cotangent := by
  let P : Algebra.Extension R R :=
    Algebra.Extension.ofSurjective f (fun r ↦ ⟨algebraMap R A r, f.commutes r⟩)
  have hmap : algebraMap P.Ring R = f.toRingHom := by
    exact RingHom.algebraMap_toAlgebra f.toRingHom
  have hker : P.ker = RingHom.ker f.toRingHom := congrArg RingHom.ker hmap
  have hP : P.ker.FG := by
    rw [hker]
    exact h
  let _ : Module.Finite R P.Cotangent :=
    Algebra.Extension.Cotangent.finite (P := P) hP
  have hfinite : Module.Finite R P.ker.Cotangent :=
    Module.Finite.equiv (P.cotangentEquivCotangentKer.restrictScalars R)
  exact Module.Finite.equiv
    ((Ideal.Cotangent.equivOfEq P.ker (RingHom.ker f.toRingHom) hker).restrictScalars R)

/-- The cotangent space at an augmented point of a noetherian algebra is finite over the base.

The augmentation hypothesis is encoded by the codomain of `f`: because `f` is an `R`-algebra
homomorphism, it is a retraction of `algebraMap R A`. -/
theorem finite_cotangent_ker (f : A →ₐ[R] R) [IsNoetherianRing A] :
    Module.Finite R (RingHom.ker f.toRingHom).Cotangent :=
  finite_cotangent_ker_of_fg f (RingHom.ker f.toRingHom).fg_of_isNoetherianRing

end AlgHom

end TauCeti



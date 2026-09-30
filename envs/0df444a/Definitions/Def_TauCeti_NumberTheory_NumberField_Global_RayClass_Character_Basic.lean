-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Character_Basic
-- name    : TauCeti_NumberTheory_NumberField_Global_RayClass_Character_Basic
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:01:29.018125+00:00
-- url     : https://prove2.me/theorems/8280f1b2-6e40-42b5-bd41-6c0dd1119bed
-- title:
--   Ray class characters
-- statement:
--   For a modulus $\mathfrak m$ of a number field $K$, a ray class character is a homomorphism
--
--   $$
--   \chi:\operatorname{Cl}_{\mathfrak m}(K)\longrightarrow\mathbb C^\times.
--   $$
--
--   It evaluates on nonzero integral ideals prime to $\mathfrak m_0$ via their ray class. These characters give the arithmetic weights used in ray-class Dirichlet series.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/Character/Basic.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/Character/Basic.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Ray class characters

A ray class character of a modulus `𝔪` is a multiplicative character of its finite ray class
group with values in the complex units.  Composing with `idealClass 𝔪` evaluates it on the
nonzero integral ideals prime to the finite part of `𝔪`; the coprimality proof remains in the
domain because `idealClass 𝔪` is defined only on those ideals.

When `𝔪 ∣ 𝔫`, pullback along the surjective transition `classMap : Cl_𝔫 → Cl_𝔪` induces a
character of the larger modulus.  These pullbacks are injective, compose along chains of moduli,
and agree with the inclusion of integral ideals prime to the larger modulus.  This is the finite
character API used in ray-class counting and in the factorization of cyclotomic Galois
characters.

## Main definitions

* `TauCeti.GlobalNumberFields.RayClassCharacter`: multiplicative complex-unit characters of a
  ray class group;
* `TauCeti.GlobalNumberFields.RayClassCharacter.onIdeals`: evaluation on integral ideals prime
  to the modulus;
* `TauCeti.GlobalNumberFields.RayClassCharacter.induced`: pullback of a character along a change
  of modulus.

## Main results

* `TauCeti.GlobalNumberFields.RayClassCharacter.ext`: a ray class character is
  determined by its values on integral ideals;
* `TauCeti.GlobalNumberFields.RayClassCharacter.induced_injective`: increasing the modulus does
  not identify distinct characters;
* `TauCeti.GlobalNumberFields.RayClassCharacter.onIdeals_induced`: change of modulus commutes
  with evaluation on ideals.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VII, §1.
-/

 section

open scoped NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- A **ray class character** of `𝔪`: a multiplicative character of `RayClassGroup 𝔪`
with values in the complex units. -/
abbrev RayClassCharacter (𝔪 : Modulus K) := RayClassGroup 𝔪 →* ℂˣ

namespace RayClassCharacter

variable {𝔪 𝔫 𝔬 : Modulus K}

/-- Evaluate a ray class character on nonzero integral ideals prime to its modulus.

The domain is `integralIdealsPrimeTo 𝔪`, rather than all integral ideals, because an ideal
meeting the finite part of the modulus has no ray class and hence no character value. -/
noncomputable def onIdeals (χ : RayClassCharacter 𝔪) : integralIdealsPrimeTo 𝔪 →* ℂˣ :=
  χ.comp (idealClass 𝔪)



















end RayClassCharacter

end TauCeti.GlobalNumberFields

end
end



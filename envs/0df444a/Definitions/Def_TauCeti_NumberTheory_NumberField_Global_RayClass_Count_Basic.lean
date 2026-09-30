-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Count_Basic
-- name    : TauCeti_NumberTheory_NumberField_Global_RayClass_Count_Basic
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:01:45.363282+00:00
-- url     : https://prove2.me/theorems/cc693ac6-4e7b-4b5e-9e20-2a41f2e5cfb4
-- title:
--   Counting the integral ideals of a ray class
-- statement:
--   For a modulus $\mathfrak m$ of a number field $K$ and a ray class $c$, define
--
--   $$
--   A_c(x)=\#\{I\ne0:I\text{ prime to }\mathfrak m_0,\ [I]_{\mathfrak m}=c,\ \mathrm N I\leq x\}.
--   $$
--
--   The ray classes partition the coprime ideals of bounded norm. These functions are the arithmetic counts in the ray-class asymptotic.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/Count/Basic.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/Count/Basic.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Counting the integral ideals of a ray class

Let `𝔪` be a modulus of a number field `K` and `c` a ray class of `𝔪`.  This file introduces
`rayClassIdealCountingFunction 𝔪 c x`, the number of nonzero integral ideals prime to the finite
part of `𝔪` that lie in the class `c` and have norm at most `x`, and proves the two facts that
make it a counting function at all: the sets being counted are finite, and summing over the ray
class group recovers the unrestricted count.

The carrier is `integralIdealsPrimeTo 𝔪`, the monoid on which `idealClass` is defined, so
coprimality and nonvanishing are forced by the type rather than imposed as side conditions; the
zero ideal and ideals sharing a prime with the finite part cannot enter the count.

Finiteness is not proved here. `TauCeti.Order.Northcott.Basic` already fixes the project's
convention
for counting by an *inclusive real* cutoff, and supplies `finite_setOf_natCast_le` for any
natural-valued Northcott function.  All this file adds is the `Northcott` instance for the absolute
norm on `integralIdealsPrimeTo 𝔪`; the finiteness, and with it `normLE`, `summatory` and
`Nat.card_coe_normLE`, then come from that shared layer.  The bound is taken in `ℝ` rather than `ℕ`
because the asymptotics that consume this count are.

The partition is stated first as an equivalence, `idealClassSigmaEquiv`, and only then in counting
form.  The equivalence needs no finiteness at all, and it is what a consumer weighting the classes
by a character reaches for; the counting statement is its `Nat.card` shadow.

## Main definitions

* `TauCeti.GlobalNumberFields.rayClassIdealCountingFunction`: the number of nonzero integral ideals
  prime to `𝔪` in a fixed ray class with norm at most `x`.
* `TauCeti.GlobalNumberFields.idealClassSigmaEquiv`: the ideals prime to `𝔪` of norm at most `x`,
  partitioned into their ray classes.

## Main results

* `TauCeti.GlobalNumberFields.sum_rayClassIdealCountingFunction`: the class counts sum to the
  unrestricted count of nonzero integral ideals prime to `𝔪` of norm at most `x`.
* `TauCeti.GlobalNumberFields.rayClassIdealCountingFunction_def`,
  `TauCeti.GlobalNumberFields.idealClassSigmaEquiv_apply_coe` and
  `TauCeti.GlobalNumberFields.idealClassSigmaEquiv_symm_apply_fst`: the characteristic lemmas of
  the two definitions, so that a consumer never has to unfold either.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* `CBirkbeck/AINTLIB` @ `2622c61d2502159c62865a1b59fc1de473519113` (Apache-2.0, Chris Birkbeck),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`:
  `card_norm_le_residue_eq_sum_class` is the corresponding partition step, stated there for the
  ordinary class group together with a norm-residue condition.
-/

 section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### Finiteness of the sets being counted -/

/-- **The absolute norm is Northcott on the ideals prime to a modulus**: only finitely many have
norm below any bound. This mirrors `TauCeti.instNorthcottAbsNormNonZeroDivisors`, which does the
same for `(Ideal R)⁰`. -/
instance (𝔪 : Modulus K) :
    Northcott (fun I : integralIdealsPrimeTo 𝔪 ↦ Ideal.absNorm (I : Ideal (𝓞 K))) where
  finite_le B :=
    (Ring.HasFiniteQuotients.finite_absNorm_le (R := 𝓞 K) B).preimage Subtype.val_injective.injOn

/-- The nonzero integral ideals prime to `𝔪` of norm at most a real bound form a finite type. The
cutoff is real, and inclusive, per the convention `TauCeti.Order.Northcott.Basic` fixes. -/
instance (𝔪 : Modulus K) (x : ℝ) :
    Finite {I : integralIdealsPrimeTo 𝔪 // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} :=
  (TauCeti.finite_setOf_natCast_le _ x).to_subtype

/-- Restricting to a single ray class keeps the set finite. -/
instance (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) :
    Finite {I : integralIdealsPrimeTo 𝔪 //
      idealClass 𝔪 I = c ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} :=
  Finite.of_injective
    (β := {I : integralIdealsPrimeTo 𝔪 // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x})
    (Subtype.map id fun _ ↦ And.right) (Subtype.map_injective _ Function.injective_id)

/-! ### The counting function and the class partition -/

/-- **The ray class ideal counting function.**  The number of nonzero integral ideals in the ray
class `c` of `𝔪`, prime to the finite part of `𝔪`, whose norm is at most `x`.  The carrier already
forces coprimality and nonvanishing, so the zero ideal and other classes cannot enter. -/
noncomputable def rayClassIdealCountingFunction
    (𝔪 : Modulus K) (c : RayClassGroup 𝔪) (x : ℝ) : ℕ :=
  Nat.card {I : integralIdealsPrimeTo 𝔪 //
    idealClass 𝔪 I = c ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x}



/-- **The ray classes partition the ideals of bounded norm.**  An ideal prime to `𝔪` of norm at
most `x` is the same thing as a ray class together with an ideal of that class and that norm
bound, because `idealClass 𝔪` is a function on the carrier and the summands are exactly its
fibres. -/
noncomputable def idealClassSigmaEquiv (𝔪 : Modulus K) (x : ℝ) :
    (Σ c : RayClassGroup 𝔪, {I : integralIdealsPrimeTo 𝔪 //
        idealClass 𝔪 I = c ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x}) ≃
      {I : integralIdealsPrimeTo 𝔪 // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} :=
  (Equiv.sigmaCongrRight fun _ ↦ (Equiv.subtypeEquivRight fun _ ↦ and_comm).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm).trans (Equiv.sigmaFiberEquiv _)







end TauCeti.GlobalNumberFields

end
end



-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Character_Sum
-- name    : TauCeti_NumberTheory_NumberField_Global_RayClass_Character_Sum
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:08:42.288293+00:00
-- url     : https://prove2.me/theorems/f3c6a090-4abf-4f96-86a7-d953acb5c433
-- title:
--   Character sums over the integral ideals of bounded norm
-- statement:
--   For a ray class character $\chi$ modulo $\mathfrak m$, its partial sum is
--
--   $$
--   A_\chi(x)=\sum_{\substack{I\ne0,\ I\text{ prime to }\mathfrak m_0\\\mathrm N I\leq x}}\chi([I]_{\mathfrak m}).
--   $$
--
--   This is the weighted version of the ray-class ideal count.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/Character/Sum.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/Character/Sum.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Character_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Count_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
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
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Valuation.Basic
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
# Character sums over the integral ideals of bounded norm

Let `𝔪` be a modulus of a number field `K` and `χ` a ray class character of `𝔪`.  This file
introduces `rayClassCharacterPartialSum 𝔪 χ x`, the sum of `χ` over the nonzero integral ideals
prime to the finite part of `𝔪` whose norm is at most `x`, and identifies it with the
`χ`-weighted combination of the ray class counting functions.

The sum ranges over ideals, not over chosen class representatives.  Regrouping it by ray class is
exactly the partition `idealClassSigmaEquiv`, and on each fibre `χ` is constant, so each class
contributes its counting function scaled by the single value `χ` takes there.

## Main definitions

* `TauCeti.GlobalNumberFields.rayClassCharacterPartialSum`: the partial sum of a ray class
  character over the integral ideals of bounded norm.

## Main results

* `TauCeti.GlobalNumberFields.rayClassCharacterPartialSum_eq_sum`: the partial sum is
  `∑ c, χ c * rayClassIdealCountingFunction 𝔪 c x`.
-/

 section

namespace TauCeti.GlobalNumberFields

open scoped NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The partial sum of a ray class character.**  The inclusive summatory function, in the sense
of `TauCeti.summatory`, of `χ.onIdeals` over the nonzero integral ideals prime to the finite part
of `𝔪`, graded by the absolute norm. -/
noncomputable def rayClassCharacterPartialSum
    (𝔪 : Modulus K) (χ : RayClassCharacter 𝔪) (x : ℝ) : ℂ :=
  summatory (fun I : integralIdealsPrimeTo 𝔪 ↦ Ideal.absNorm (I : Ideal (𝓞 K)))
    (fun I ↦ (χ.onIdeals I : ℂ)) x





end TauCeti.GlobalNumberFields

end
end



-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Counting_Ray_Ideal_Set
-- name    : TauCeti_NumberTheory_NumberField_Global_Counting_Ray_Ideal_Set
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:25:49.159826+00:00
-- url     : https://prove2.me/theorems/8e5808ae-49da-4c03-9f41-194acd769203
-- title:
--   Elements of an ideal congruent to one, in the ray fundamental domain
-- statement:
--   For a modulus $\mathfrak m$ and an integral ideal $\mathfrak a$, the ray ideal set consists of mixed images of elements $a\in\mathfrak a$ lying in the ray fundamental domain and satisfying
--
--   $$
--   a\equiv1\pmod{\mathfrak m_0}.
--   $$
--
--   It identifies the relevant ideal elements with a subset of the ray integer set.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/Counting/Ray/Ideal/Set.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/Counting/Ray/Ideal/Set.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Counting_RayFundamentalDomain_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Counting_RayFundamentalDomain_IntegerSet
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
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
# Elements of an ideal congruent to one, in the ray fundamental domain

For a modulus `𝔪` with finite part `𝔪₀` and a nonzero integral ideal `𝔞`, this file names the set
of points of the ray fundamental domain of `𝔪` that are images of elements of `𝔞` congruent to
one modulo `𝔪₀`, and records two descriptions of it.

Only the finite part appears in the set-builder: the conditions the infinite part imposes are
already carried by the ray fundamental domain, which lies in `posRegion 𝔪`
(`mem_posRegion_of_mem_rayFundamentalDomain`).

Nothing here asks that `𝔞` represent a given ray class, nor divides out the congruence roots of
unity acting on the domain; a ray-class ideal count imposes both itself.

## Main definitions

* `TauCeti.GlobalNumberFields.rayIdealSet`: the set described above;
* `TauCeti.GlobalNumberFields.rayIdealSetEquiv`: a bijection from it onto the points of
  `rayIntegerSet 𝔪` whose underlying algebraic integer lies in `𝔞` and is congruent to one
  modulo `𝔪₀`, with `rayIdealSetEquiv_apply` and `rayIdealSetEquiv_symm_apply` for the two
  directions.

## Main results

* `TauCeti.GlobalNumberFields.mem_rayIdealSet`: its points, unfolded;
* `TauCeti.GlobalNumberFields.rayIdealSet_one`: the trivial modulus recovers Mathlib's
  `NumberField.mixedEmbedding.fundamentalCone.idealSet`;
* `TauCeti.GlobalNumberFields.rayIdealSet_eq_inter_vadd`: the same set as a translate of the
  congruence lattice, intersected with the domain;
* `TauCeti.GlobalNumberFields.rayIdealSet_subset_rayIntegerSet` and
  `TauCeti.GlobalNumberFields.preimageOfMemRayIntegerSet_mem_and_sub_one_mem_of_mem_rayIdealSet`:
  its points lie in `rayIntegerSet 𝔪`, and the algebraic integer each of them is the image of
  lies in `𝔞` and is congruent to one modulo `𝔪₀`.

## Implementation notes

The set takes no base point, while its description as a translate does, which is why
`rayIdealSet_eq_inter_vadd` takes a witness `ξ`.  Taking `ξ = 0` would describe a different set
instead of dispensing with the witness: `coe_congruenceLattice_mk0_eq_image`
identifies `congruenceLattice 𝔪 (FractionalIdeal.mk0 K 𝔞)` with the image of `𝔞 * 𝔪₀`, and an
element of `𝔞 * 𝔪₀` congruent to one modulo `𝔪₀` forces `1 ∈ 𝔪₀`, so the two agree only for a
trivial finite part.

## References

* `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/FundamentalCone.lean`: the `idealSet` and
  `idealSetEquiv` layer there is the model for this file, with the fundamental cone replaced by
  the ray fundamental domain and the congruence condition added.
-/

 section

open NumberField NumberField.mixedEmbedding

open scoped Pointwise nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The images, inside the ray fundamental domain of `𝔪`, of the elements of `𝔞` that are
congruent to one modulo the finite part of `𝔪`.  This is the ray analogue of
`NumberField.mixedEmbedding.fundamentalCone.idealSet`. -/
def rayIdealSet (𝔪 : Modulus K) (𝔞 : (Ideal (𝓞 K))⁰) : Set (mixedSpace K) :=
  rayFundamentalDomain 𝔪 ∩ (fun y : 𝓞 K ↦ mixedEmbedding K (y : K)) ''
      {α : 𝓞 K | α ∈ (𝔞 : Ideal (𝓞 K)) ∧ α - 1 ∈ 𝔪.finitePart}

/-- **The points of `rayIdealSet`.**  A point lies in it exactly when it lies in the ray
fundamental domain and is the image of an element of `𝔞` congruent to one modulo `𝔪₀`. -/
theorem mem_rayIdealSet {𝔪 : Modulus K} {𝔞 : (Ideal (𝓞 K))⁰} {x : mixedSpace K} :
    x ∈ rayIdealSet 𝔪 𝔞 ↔ x ∈ rayFundamentalDomain 𝔪 ∧
      ∃ α : 𝓞 K, (α ∈ (𝔞 : Ideal (𝓞 K)) ∧ α - 1 ∈ 𝔪.finitePart) ∧ mixedEmbedding K (α : K) = x :=
  Iff.rfl





/-- Every point of `rayIdealSet 𝔪 𝔞` lies in `rayIntegerSet 𝔪`: it lies in the ray fundamental
domain and is the image of an algebraic integer.  Both the membership in `𝔞` and the congruence
condition are forgotten.

This inclusion is what lets `rayIdealSetEquiv` land in a subtype of `rayIntegerSet 𝔪`; Mathlib
packages the corresponding map as a definition,
`NumberField.mixedEmbedding.fundamentalCone.idealSetMap`. -/
theorem rayIdealSet_subset_rayIntegerSet (𝔪 : Modulus K) (𝔞 : (Ideal (𝓞 K))⁰) :
    rayIdealSet 𝔪 𝔞 ⊆ rayIntegerSet 𝔪 := by
  rintro x ⟨hdom, α, -, rfl⟩
  exact mem_rayIntegerSet.mpr ⟨hdom, α, rfl⟩

/-- The algebraic integer underlying a point of `rayIdealSet 𝔪 𝔞` lies in `𝔞` and is congruent to
one modulo `𝔪₀`.

With `rayIdealSet_subset_rayIntegerSet`, this is what makes `rayIdealSetEquiv` well defined.  The
conjunction is stated bundled because it is the predicate defining the set `rayIdealSet` is built
from, and is verbatim the subtype predicate of that equivalence's codomain. -/
theorem preimageOfMemRayIntegerSet_mem_and_sub_one_mem_of_mem_rayIdealSet {𝔪 : Modulus K}
    {𝔞 : (Ideal (𝓞 K))⁰} {a : rayIntegerSet 𝔪} (ha : (a : mixedSpace K) ∈ rayIdealSet 𝔪 𝔞) :
    (preimageOfMemRayIntegerSet a : 𝓞 K) ∈ (𝔞 : Ideal (𝓞 K)) ∧
      (preimageOfMemRayIntegerSet a : 𝓞 K) - 1 ∈ 𝔪.finitePart := by
  obtain ⟨b, hb⟩ := a
  obtain ⟨-, α, hα, rfl⟩ := ha
  rw [preimageOfMemRayIntegerSet_mixedEmbedding]
  exact hα

/-- **`rayIdealSet` as a subtype of the ray integer set.**  A point of `rayIntegerSet 𝔪` comes
from a point of `rayIdealSet 𝔪 𝔞` exactly when the algebraic integer it is the image of lies in
`𝔞` and is congruent to one modulo `𝔪₀`, so the two carriers are in bijection.

This is the ray analogue of `NumberField.mixedEmbedding.fundamentalCone.idealSetEquiv`, with the
forward map applied inline rather than named separately. -/
noncomputable def rayIdealSetEquiv (𝔪 : Modulus K) (𝔞 : (Ideal (𝓞 K))⁰) : rayIdealSet 𝔪 𝔞 ≃
    {a : rayIntegerSet 𝔪 // (preimageOfMemRayIntegerSet a : 𝓞 K) ∈ (𝔞 : Ideal (𝓞 K)) ∧
      (preimageOfMemRayIntegerSet a : 𝓞 K) - 1 ∈ 𝔪.finitePart} :=
  Equiv.ofBijective
    (fun x ↦ ⟨⟨(x : mixedSpace K), rayIdealSet_subset_rayIntegerSet 𝔪 𝔞 x.prop⟩,
      preimageOfMemRayIntegerSet_mem_and_sub_one_mem_of_mem_rayIdealSet x.prop⟩)
    ⟨fun _ _ h ↦ Subtype.ext (congrArg (fun y ↦ ((y.1 : rayIntegerSet 𝔪) : mixedSpace K)) h),
      fun a ↦ ⟨⟨(a : mixedSpace K), mem_rayIdealSet.mpr
        ⟨(mem_rayIntegerSet.mp (a : rayIntegerSet 𝔪).prop).1,
          preimageOfMemRayIntegerSet (a : rayIntegerSet 𝔪), a.prop,
            mixedEmbedding_preimageOfMemRayIntegerSet _⟩⟩,
        Subtype.ext (Subtype.ext rfl)⟩⟩





end TauCeti.GlobalNumberFields

end
end



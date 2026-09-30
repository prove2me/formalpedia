-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Counting_CongruenceLattice
-- name    : TauCeti_NumberTheory_NumberField_Global_Counting_CongruenceLattice
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:56:22.098697+00:00
-- url     : https://prove2.me/theorems/0d3eb83b-f219-44c4-b035-e6023f8cb2bf
-- title:
--   The congruence lattice of a modulus
-- statement:
--   For a modulus $\mathfrak m$ and a nonzero fractional ideal $I$ of a number field, the congruence lattice is the image of $I\mathfrak m_0$ under the mixed embedding. It is a discrete full integer lattice. Its cosets encode congruence conditions in geometric ideal counting.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/Counting/CongruenceLattice.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/Counting/CongruenceLattice.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.FractionalIdeal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
# The congruence lattice of a modulus

Let `𝔪` be a modulus of a number field `K` with finite part `𝔪₀`, and let `I` be an invertible
fractional ideal.  Under the mixed embedding `K → ℝ^r₁ × ℂ^r₂`, the ideal `I` becomes the full
lattice `mixedEmbedding.idealLattice K I`.  The **congruence lattice** `congruenceLattice 𝔪 I` is
the sublattice coming from `I * 𝔪₀`: the elements of `I` congruent to `0` modulo `I * 𝔪₀`.

Counting the elements of `I` in a region that satisfy a congruence `x ≡ a mod I * 𝔪₀` is
counting the points of one coset of this sublattice, which is itself a translate of a full
lattice.  The index computation below says that there are exactly `N 𝔪₀` such cosets, and the
covolume grows by the factor `N 𝔪₀`.  These are the lattice inputs to counting integral ideals in
a ray class.

Only the finite part `𝔪₀` enters the lattice: the infinite part of `𝔪` plays no role here, and
the sign conditions at the real places of `𝔪.infinitePart` are imposed by the region, not by the
sublattice.

## Main definitions

* `TauCeti.GlobalNumberFields.congruenceLattice`: the lattice of `I * 𝔪₀` in the mixed space.

## Main results

* `TauCeti.GlobalNumberFields.mem_congruenceLattice_iff`: its points are the images of the
  elements of `I * 𝔪₀`.
* `TauCeti.GlobalNumberFields.coe_congruenceLattice_mk0_eq_image`: for an integral ideal `𝔞`,
  the same description over `𝔞 * 𝔪₀`.
* `TauCeti.GlobalNumberFields.congruenceLattice_le_idealLattice`: it is a sublattice of the ideal
  lattice of `I`.
* `TauCeti.GlobalNumberFields.relIndex_congruenceLattice`: its index in the ideal lattice of `I`
  is the absolute norm of `𝔪₀`.
* `TauCeti.GlobalNumberFields.covolume_congruenceLattice`: its covolume is `N 𝔪₀` times the
  covolume of the ideal lattice of `I`.
* `TauCeti.GlobalNumberFields.covolume_congruenceLattice_div_absNorm`: its covolume divided by
  `N I` is `N 𝔪₀ · √|d_K| / 2 ^ r₂`.
* `TauCeti.GlobalNumberFields.congruenceLattice_eq_of_finitePart_eq`: it depends only on the
  finite part of the modulus.
* `TauCeti.GlobalNumberFields.congruenceLattice_eq_idealLattice_of_finitePart_eq_top`: for a
  modulus with trivial finite part it is the ideal lattice itself; `congruenceLattice_one` and
  `congruenceLattice_narrowModulus` are the cases of the trivial and the narrow modulus.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

 section

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The **congruence lattice** of a modulus `𝔪` inside the ideal lattice of `I`: the image in the
mixed space of the fractional ideal `I * 𝔪₀`, whose elements are those of `I` congruent to `0`
modulo `I * 𝔪₀`, where `𝔪₀` is the finite part of `𝔪`. -/
noncomputable def congruenceLattice (𝔪 : Modulus K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (mixedSpace K) :=
  idealLattice K
    (I * FractionalIdeal.mk0 K ⟨𝔪.finitePart, mem_nonZeroDivisors_of_ne_zero 𝔪.finitePart_ne_zero⟩)



/-- The congruence lattice is a discrete subgroup of the mixed space. -/
instance (𝔪 : Modulus K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    DiscreteTopology (congruenceLattice 𝔪 I) := by
  unfold congruenceLattice
  infer_instance

open scoped Classical in
/-- The congruence lattice is a full `ℤ`-lattice in the mixed space. -/
instance (𝔪 : Modulus K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsZLattice ℝ (congruenceLattice 𝔪 I) := by
  unfold congruenceLattice
  infer_instance





















end TauCeti.GlobalNumberFields

end
end



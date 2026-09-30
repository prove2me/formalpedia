-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Exact
-- name    : TauCeti_NumberTheory_NumberField_Global_RayClass_Exact
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:23:34.953387+00:00
-- url     : https://prove2.me/theorems/d8454b1e-c0ce-478e-8d15-5297fce6bf31
-- title:
--   The ray class exact sequence
-- statement:
--   For a modulus $\mathfrak m$ of a number field $K$, this bundle defines the maps from integer units to residue units and signs, from those data to principal ray classes, and from ray classes to ordinary ideal classes. These are the maps in the ray-class exact sequence.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/Exact.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/Exact.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Order_Ring_Units
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Approximation_Weak
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_CongruenceQuotient
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Residue
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_NumberTheory_NumberField_SignApproximation
import Definitions.Def_TauCeti_NumberTheory_NumberField_Units_Signature_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Units_Signature_Integer
import Definitions.Def_TauCeti_RingTheory_ClassGroup_Basic
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Definitions.Def_TauCeti_RingTheory_Ideal_Quotient_Representative
import Definitions.Def_TauCeti_RingTheory_Valuation_AbsoluteValue
import Definitions.Def_TauCeti_RingTheory_Valuation_Approximation
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
# The ray class exact sequence

For a modulus `m` of a number field `K`, forgetting its congruence and sign conditions sends a ray
class to an ordinary ideal class.  This file constructs the full exact sequence

```text
1 → unitsCongruenceSubgroup m → (𝓞 K)ˣ → A m → RayClassGroup m → ClassGroup (𝓞 K) → 1,
```

where `A m = (𝓞 K ⧸ m.finitePart)ˣ × (m.infinitePart → ℤˣ)` records residues and prescribed
signs.  It also retains the useful coarser exact tail
`primeToSubgroup m → RayClassGroup m → ClassGroup (𝓞 K) → 1`.

In the coarser tail, the first map sends an element of `Kˣ` that is a unit at the finite part to
the ray class of its principal ideal.  The second map is surjective, and its kernel is exactly the
range of the first.  Surjectivity of the transition maps follows by weak approximation, and
surjectivity onto the ordinary class group follows by transition to the trivial modulus.

The kernel of `A m → RayClassGroup m` is the image of the integer units, while the kernel of the
map from integer units to `A m` is `unitsCongruenceSubgroup m`.  The resulting exact sequence is
the input to the ray class number formula.

## Main definitions

* `TauCeti.GlobalNumberFields.principalRayClass`: the ray class of a principal fractional ideal
  whose generator is a unit at the finite part.
* `TauCeti.GlobalNumberFields.rayClassToClassGroup`: the ordinary ideal class underlying a ray
  class.
* `TauCeti.GlobalNumberFields.unitsResidueSignHom`: the residues and signs of the integer units.
* `TauCeti.GlobalNumberFields.residueSignRayClass`: the principal ray class of a residue unit and
  sign pattern.

## Main results

* `TauCeti.GlobalNumberFields.rayClassToClassGroup_surjective`: every ordinary ideal class lifts
  to a ray class.
* `TauCeti.GlobalNumberFields.ker_rayClassToClassGroup`: the kernel consists exactly of ray
  classes of principal ideals generated by elements in `primeToSubgroup m`.
* `TauCeti.GlobalNumberFields.mulExact_principalRayClass_rayClassToClassGroup`: the corresponding
  multiplicative exactness statement.
* `TauCeti.GlobalNumberFields.classMap_surjective`: every transition between ray class groups is
  surjective.
* `TauCeti.GlobalNumberFields.ker_unitsResidueSignHom`,
  `TauCeti.GlobalNumberFields.ker_residueSignRayClass` and
  `TauCeti.GlobalNumberFields.range_residueSignRayClass`: the three nontrivial exactness statements
  in the full sequence.
* `TauCeti.GlobalNumberFields.mulExact_unitsCongruenceSubgroup_unitsResidueSignHom`,
  `TauCeti.GlobalNumberFields.mulExact_unitsResidueSignHom_residueSignRayClass` and
  `TauCeti.GlobalNumberFields.mulExact_residueSignRayClass_rayClassToClassGroup`: their
  multiplicative exactness forms.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

 section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- The ray class of the principal ideal generated by an element that is a unit at every prime
dividing the finite part of `m`. -/
noncomputable def principalRayClass (m : Modulus K) :
    primeToSubgroup m →* RayClassGroup m :=
  (rayClassMk m).comp (principalIdealPrimeTo m)

/-- The principal ray class is represented by the corresponding principal fractional ideal. -/
@[simp] theorem principalRayClass_apply (m : Modulus K) (x : primeToSubgroup m) :
    principalRayClass m x = rayClassMk m (principalIdealPrimeTo m x) :=
  (rfl)

/-- A generator congruent to one modulo `m` has trivial principal ray class. -/
theorem principalRayClass_eq_one_of_isCongrOne {m : Modulus K} {x : primeToSubgroup m}
    (hx : IsCongrOne m (x : Kˣ)) : principalRayClass m x = 1 := by
  rw [principalRayClass_apply, rayClassMk_eq_one_iff, mem_ray_iff]
  exact ⟨(x : Kˣ), hx, coe_principalIdealPrimeTo m x |>.symm⟩

/-- The map from a ray class to its underlying ordinary ideal class. -/
noncomputable def rayClassToClassGroup (m : Modulus K) :
    RayClassGroup m →* ClassGroup (RingOfIntegers K) :=
  rayClassLift (idealsPrimeToClassGroup m) fun I hI ↦ by
    rw [MonoidHom.mem_ker]
    obtain ⟨x, _, hx⟩ := mem_ray_iff.mp hI
    rw [idealsPrimeToClassGroup_apply, ← hx]
    exact ClassGroup.mk_toPrincipalIdeal x













/-! ### The residue-and-sign presentation of the exact sequence -/



/-- **The residues and signs of the integer units.**  This is the left-hand map of the ray class
exact sequence; its image is the obstruction that is divided out of the residue units and signs
before they embed into the ray class group. -/
noncomputable def unitsResidueSignHom (𝔪 : Modulus K) :
    (𝓞 K)ˣ →* (𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ) :=
  (residueSignHom 𝔪).comp (unitsToPrimeToSubgroup 𝔪)







/-- **The principal ray class of a residue unit and a sign pattern.**  The principal ray class of
an element prime to `𝔪` depends only on its residue modulo the finite part and its signs at the
real places of `𝔪`, and every residue unit and sign pattern arises (`residueSignEquiv`); this is
the induced homomorphism. -/
noncomputable def residueSignRayClass (𝔪 : Modulus K) :
    (𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ) →* RayClassGroup 𝔪 :=
  (QuotientGroup.lift _ (principalRayClass 𝔪) fun _ hx ↦ MonoidHom.mem_ker.mpr <|
      principalRayClass_eq_one_of_isCongrOne
        (mem_congruenceSubgroup.mp (Subgroup.mem_subgroupOf.mp hx))).comp
    (residueSignEquiv 𝔪).symm.toMonoidHom













end TauCeti.GlobalNumberFields

end
end



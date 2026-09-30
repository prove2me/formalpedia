-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_CongruenceQuotient
-- name    : TauCeti_NumberTheory_NumberField_Global_RayClass_CongruenceQuotient
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:16:45.701041+00:00
-- url     : https://prove2.me/theorems/7af4c16b-ece9-466a-a433-43ab3b5e0912
-- title:
--   The residue-and-sign presentation of the congruence quotient
-- statement:
--   For a modulus $\mathfrak m$ of a number field $K$, residue classes and signs give the quotient description
--
--   $$
--   K^\times_{\mathfrak m_0}/K^\times_{\mathfrak m,1}
--   \simeq(\mathcal O_K/\mathfrak m_0)^\times\times\prod_{\tau\in\mathfrak m_\infty}\{\pm1\}.
--   $$
--
--   Here the numerator consists of elements that are units at primes dividing $\mathfrak m_0$, and the denominator consists of elements congruent to one modulo the full modulus. This separates the finite and real-place conditions.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/CongruenceQuotient.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/CongruenceQuotient.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Order_Ring_Units
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Approximation_Weak
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Residue
import Definitions.Def_TauCeti_NumberTheory_NumberField_SignApproximation
import Definitions.Def_TauCeti_NumberTheory_NumberField_Units_Signature_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Units_Signature_Integer
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
# The residue-and-sign presentation of the congruence quotient

Let `𝔪` be a modulus of a number field `K`.  Congruence to one modulo `𝔪` is two independent
conditions on an element of `primeToSubgroup 𝔪`: reduction to one in `(𝓞 K ⧸ 𝔪.finitePart)ˣ`, and
positivity at each real place selected by `𝔪.infinitePart`.  This file packages the two conditions
into one homomorphism

```text
residueSignHom 𝔪 :
  primeToSubgroup 𝔪 →* (𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ)
```

and proves that it is surjective with kernel exactly `congruenceSubgroup 𝔪`.  The resulting
isomorphism `residueSignEquiv` computes the relative index

```text
(congruenceSubgroup 𝔪).relIndex (primeToSubgroup 𝔪)
  = Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ 𝔪.infinitePart.card,
```

which is the residue-and-sign factor of the ray class number formula — the factor *before* the
image of the global units is divided out — and strengthens the bare finiteness recorded by
`congruenceSubgroup_finiteIndex`.

Surjectivity is the arithmetic content and is *not* a chinese-remainder statement: the residue
class and the signs have to be realized by one and the same element of `Kˣ`, so the proof runs
through weak approximation at the mixed set of places consisting of the primes dividing
`𝔪.finitePart` together with all real places
(`exists_fieldUnit_valuation_sub_lt_and_signHom_eq`).  An approximation to a chosen integral
representative of the residue class, closely enough that `v.valuation K` of their difference stays
below `exp (-𝔪.exponent v)` at each prime of the support, has the same reduction as that
representative: the quotient of the two then differs from one by at most that much, which is the
congruence condition recorded by `residue_eq_one_iff`.

The global units of `K` are nowhere quotiented out here.  Their image in this quotient is the
obstruction that glues the residue-unit and sign factors to the ordinary class group inside the
ray class group, and it is why the ray class group is not the product of the three.

## Main definitions

* `TauCeti.GlobalNumberFields.residueSignHom`: the reduction-and-signs homomorphism.
* `TauCeti.GlobalNumberFields.residueSignEquiv`: the induced isomorphism from the congruence
  quotient.

## Main results

* `TauCeti.GlobalNumberFields.residueSignHom_eq_one_iff` and
  `TauCeti.GlobalNumberFields.ker_residueSignHom`: the kernel is the congruence subgroup.
* `TauCeti.GlobalNumberFields.residueSignHom_surjective`: every residue unit and sign pattern is
  realized simultaneously, together with its archimedean half
  `TauCeti.GlobalNumberFields.modulusSignHom_comp_primeToSubgroup_surjective`.
* `TauCeti.GlobalNumberFields.relIndex_congruenceSubgroup`: the exact relative index.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

 section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### The signs prescribed by a modulus -/

/-- **The signs of a field unit at the real places selected by a modulus.**  This is `signHom`
restricted to `𝔪.infinitePart`; the real places outside the modulus are unconstrained and are
forgotten. -/
noncomputable def modulusSignHom (𝔪 : Modulus K) : Kˣ →* (𝔪.infinitePart → ℤˣ) where
  toFun x w := signHom x w.1
  map_one' := funext fun w ↦ by rw [map_one, Pi.one_apply, Pi.one_apply]
  map_mul' x y := funext fun w ↦ by rw [map_mul, Pi.mul_apply, Pi.mul_apply]

@[simp] theorem modulusSignHom_apply (𝔪 : Modulus K) (x : Kˣ) (w : 𝔪.infinitePart) :
    modulusSignHom 𝔪 x w = signHom x w.1 := (rfl)

/-- **The prescribed signs are trivial exactly at an element positive on the infinite part.** -/
@[simp] theorem modulusSignHom_eq_one_iff {𝔪 : Modulus K} (x : Kˣ) :
    modulusSignHom 𝔪 x = 1 ↔
      ∀ w ∈ 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.2 (x : K) := by
  rw [funext_iff]
  refine ⟨fun h w hw ↦ ?_, fun h w ↦ ?_⟩
  · exact (signHom_apply_eq_one_iff x ⟨w, w.2⟩).mp (h ⟨w, hw⟩)
  · exact (signHom_apply_eq_one_iff x w.1).mpr (h w.1 w.2)

/-! ### The reduction-and-signs homomorphism -/

/-- **The residue-and-sign presentation of a modulus.**  An element of `Kˣ` that is a unit at every
prime dividing `𝔪.finitePart` has both a reduction in `(𝓞 K ⧸ 𝔪.finitePart)ˣ` and a sign at each
real place selected by `𝔪`; congruence to one modulo `𝔪` is exactly the vanishing of both.

The two factors are the finite and the archimedean halves of the ray class number formula. -/
noncomputable def residueSignHom (𝔪 : Modulus K) :
    primeToSubgroup 𝔪 →* (𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ) :=
  (residueHom 𝔪).prod ((modulusSignHom 𝔪).comp (primeToSubgroup 𝔪).subtype)

@[simp] theorem residueSignHom_fst (𝔪 : Modulus K) (x : primeToSubgroup 𝔪) :
    (residueSignHom 𝔪 x).1 = residueHom 𝔪 x := (rfl)

@[simp] theorem residueSignHom_snd (𝔪 : Modulus K) (x : primeToSubgroup 𝔪) :
    (residueSignHom 𝔪 x).2 = modulusSignHom 𝔪 (x : Kˣ) := (rfl)

/-- **Congruence to one is exactly trivial reduction together with trivial signs.** -/
@[simp] theorem residueSignHom_eq_one_iff {𝔪 : Modulus K} (x : primeToSubgroup 𝔪) :
    residueSignHom 𝔪 x = 1 ↔ (x : Kˣ) ∈ congruenceSubgroup 𝔪 := by
  rw [Prod.ext_iff, mem_congruenceSubgroup, isCongrOne_iff, Prod.fst_one, Prod.snd_one,
    residueSignHom_fst, residueSignHom_snd, modulusSignHom_eq_one_iff]
  refine and_congr_left fun hpos ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine (residue_eq_one_iff x).mp ?_
    rw [← coe_residueHom 𝔪 x, h, Units.val_one]
  · exact residueHom_eq_one_of_mem_congruenceSubgroup
      (mem_congruenceSubgroup.mpr (isCongrOne_iff.mpr ⟨h, hpos⟩))

/-- **The kernel of the residue-and-sign presentation is the congruence subgroup.** -/
theorem ker_residueSignHom (𝔪 : Modulus K) :
    (residueSignHom 𝔪).ker = (congruenceSubgroup 𝔪).subgroupOf (primeToSubgroup 𝔪) := by
  ext x
  rw [MonoidHom.mem_ker, residueSignHom_eq_one_iff, Subgroup.mem_subgroupOf]

/-! ### Surjectivity -/

/-- **The residue-and-sign presentation is surjective.**  Every residue unit modulo the finite part
and every pattern of signs at the real places of the modulus are realized simultaneously by one
element of `Kˣ` that is a unit at the finite part.

The two prescriptions are independent: no compatibility between a residue class and a sign pattern
is required, which is what makes the congruence quotient a direct product. -/
theorem residueSignHom_surjective (𝔪 : Modulus K) : Function.Surjective (residueSignHom 𝔪) := by
  -- Weak approximation at the primes of `𝔪.support` together with all the real places: approximate
  -- an integral representative of `u` closely enough to share its reduction, with the signs of `ε`.
  classical
  rintro ⟨u, ε⟩
  obtain ⟨⟨α, hα⟩, hαu⟩ := residueHom_surjective 𝔪 u
  -- Extend the prescribed signs by `1` at the real places outside the modulus.
  obtain ⟨x, hxα, hxs⟩ := exists_fieldUnit_valuation_sub_lt_and_signHom_eq (S := 𝔪.support)
    (fun _ ↦ (α : K)) (fun v ↦ WithZero.exp (-(𝔪.exponent v : ℤ)))
    (fun _ _ ↦ WithZero.exp_ne_zero)
    (fun w ↦ if h : w ∈ 𝔪.infinitePart then ε ⟨w, h⟩ else 1)
  -- The approximation is close enough to `α` to have its valuation at the support.
  have hxα' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.finitePart →
      v.valuation K ((x : K) - (α : K)) < v.valuation K (α : K) := fun v hv ↦ by
    rw [mem_primeToSubgroup.mp hα v hv]
    exact lt_of_lt_of_le (hxα v ((Modulus.mem_support_iff 𝔪 v).mpr hv))
      (by
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        exact neg_nonpos.mpr (Int.natCast_nonneg _))
  have hx : x ∈ primeToSubgroup 𝔪 := mem_primeToSubgroup.mpr fun v hv ↦ by
    rw [Valuation.map_eq_of_sub_lt (v.valuation K) (hxα' v hv)]
    exact mem_primeToSubgroup.mp hα v hv
  refine ⟨⟨x, hx⟩, Prod.ext ?_ ?_⟩
  · -- The quotient of the approximation by the representative reduces to one.
    have hquot : residueHom 𝔪 (⟨x, hx⟩ * ⟨α, hα⟩⁻¹) = 1 := by
      refine Units.ext ?_
      rw [coe_residueHom, Units.val_one]
      refine (residue_eq_one_iff _).mpr fun v hv ↦ ?_
      have hval : (((⟨x, hx⟩ * ⟨α, hα⟩⁻¹ : primeToSubgroup 𝔪) : Kˣ) : K) - 1 =
          ((x : K) - (α : K)) / (α : K) := by
        rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv, Units.val_inv_eq_inv_val]
        field_simp
      rw [hval, map_div₀, mem_primeToSubgroup.mp hα v hv, div_one]
      exact le_of_lt (hxα v ((Modulus.mem_support_iff 𝔪 v).mpr hv))
    rw [map_mul, map_inv, hαu, mul_inv_eq_one] at hquot
    rw [residueSignHom_fst, hquot]
  · rw [residueSignHom_snd]
    funext w
    rw [modulusSignHom_apply, hxs]
    exact dif_pos w.2



/-! ### The congruence quotient and its order -/

/-- **The congruence quotient of a modulus is the residue units times the prescribed signs.**  This
is the presentation of `primeToSubgroup 𝔪 ⧸ congruenceSubgroup 𝔪` that the ray class number formula
is read off, and it is where the finite and the archimedean data of a modulus become independent
coordinates. -/
noncomputable def residueSignEquiv (𝔪 : Modulus K) :
    primeToSubgroup 𝔪 ⧸ (congruenceSubgroup 𝔪).subgroupOf (primeToSubgroup 𝔪) ≃*
      (𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_residueSignHom 𝔪).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (residueSignHom_surjective 𝔪))





end TauCeti.GlobalNumberFields

end
end



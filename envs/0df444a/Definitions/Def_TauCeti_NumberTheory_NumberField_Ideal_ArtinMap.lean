-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_ArtinMap
-- name    : TauCeti_NumberTheory_NumberField_Ideal_ArtinMap
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:49:42.418894+00:00
-- url     : https://prove2.me/theorems/531dbd57-58fd-4cd4-af06-303f52d14154
-- title:
--   The ideal-theoretic Artin map away from a finite set of primes
-- statement:
--   For an abelian extension $L/K$, unramified prime ideals have Artin automorphisms in $\operatorname{Gal}(L/K)$. Outside a finite set containing the ramified primes, these extend multiplicatively to an ideal-theoretic Artin map
--
--   $$
--   I^S\longrightarrow\operatorname{Gal}(L/K).
--   $$
--
--   Here $I^S$ is the group of fractional ideals prime to $S$. This is the map later factored through a ray class group.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Ideal/ArtinMap.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Ideal/ArtinMap.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_FieldTheory_Galois_Abelian
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_NumberTheory_NumberField_Frobenius
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Definitions.Def_TauCeti_RingTheory_Frobenius
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The ideal-theoretic Artin map away from a finite set of primes

Let `L/K` be a finite abelian extension of number fields and let `S` be a finite set of finite
places of `K` outside which `L/K` is unramified. At a prime `v ∉ S` the Artin symbol is a
conjugacy class in an abelian group, hence a single automorphism, and extending that assignment
multiplicatively over the unique factorization of fractional ideals gives the **Artin map**

`artinHomAway : idealsAway S →* (L ≃ₐ[K] L)`

on the group `idealsAway S` of invertible fractional ideals of multiplicity zero along `S`.

The excluded set `S` is a parameter: no relation between `S` and the ramified primes is assumed
beyond the hypothesis `hur` that every prime outside `S` is unramified. Specializing `S` to the
support of the relative discriminant, or to the support of a modulus, is a separate matter.

Commutativity of `Gal(L/K)` enters as an explicit hypothesis `hab` rather than as an instance,
because the ambient group is a Galois group of a general extension. Where the construction needs
a bundled commutative structure — for the bijection between the group and its conjugacy classes,
and for the finitely supported product over all primes — the scoped `Group` plus
`IsMulCommutative` instance supplies it.

Nothing about the kernel, the image, or a factorization through ray class groups is proved here.

The construction follows Jürgen Neukirch, *Algebraic Number Theory*, Chapter VI, §7.

## Main definitions

* `TauCeti.NumberFieldArithmetic.artinElement`: the Artin automorphism at an unramified prime.
* `TauCeti.NumberFieldArithmetic.artinElementAway`: the local Artin automorphism, extended by `1`
  on `S`.
* `TauCeti.NumberFieldArithmetic.artinHomAway`: the Artin map on `idealsAway S`.
* `TauCeti.NumberFieldArithmetic.artinHomAwayIntegral`: its restriction to the integral ideals
  prime to `S`.

## Main results

* `TauCeti.NumberFieldArithmetic.artinHomAway_apply`: the value at an ideal is the product of the
  local Artin automorphisms with the multiplicities of the ideal as exponents.
* `TauCeti.NumberFieldArithmetic.artinHomAway_apply_prime`: the value at a prime outside `S` is
  the Frobenius there.
* `TauCeti.NumberFieldArithmetic.artinHomAway_eq_of_apply_prime`: those values determine the map.
* `TauCeti.NumberFieldArithmetic.artinHomAway_mono`: enlarging `S` restricts the map.
* `TauCeti.NumberFieldArithmetic.artinHomAway_restrict`: restriction of automorphisms to an
  intermediate field carries the Artin map of `L/K` to the Artin map of `M/K`.
-/

 section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField IsMulCommutative

namespace TauCeti.NumberFieldArithmetic

variable {K : Type*} [Field K] [NumberField K]

section ArtinHomAway

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
  (S : Finset (HeightOneSpectrum (𝓞 K)))
  (hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)

open scoped Classical in
/-- The Artin automorphism at an unramified prime of `K` in an abelian extension `L/K`.

This is the unique element of the Artin symbol, taken through the bijection
`ConjClasses.mkEquiv` between an abelian group and its conjugacy classes. -/
noncomputable def artinElement (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
    (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q) : L ≃ₐ[K] L :=
  letI := isMulCommutative_galoisGroup_of_commute hab
  ConjClasses.mkEquiv.symm (artinSymbol (L := L) 𝔭 hur)

/-- At an unramified prime, the Artin automorphism represents the Artin symbol. -/
theorem artinSymbol_eq_mk_artinElement (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    artinSymbol (L := L) 𝔭 hur = ConjClasses.mk (artinElement hab 𝔭 hur) := by
  let _ := isMulCommutative_galoisGroup_of_commute hab
  exact (ConjClasses.mkEquiv.apply_symm_apply _).symm

include hab in
/-- The Artin automorphism at an unramified prime is an arithmetic Frobenius at every prime
above it. -/
theorem isArithFrobAt_artinElement (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭] :
    IsArithFrobAt (𝓞 K) (artinElement hab 𝔭 hur) Q := by
  let _ := isMulCommutative_galoisGroup_of_commute hab
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q
    (Ideal.ne_bot_of_liesOver_of_ne_bot (NeZero.ne 𝔭) Q)
  have hconj : IsConj (artinElement hab 𝔭 hur) σ :=
    ConjClasses.mk_eq_mk_iff_isConj.mp <|
      (artinSymbol_eq_mk_artinElement hab 𝔭 hur).symm.trans
        (artinSymbol_eq_mk_of_isArithFrobAt 𝔭 hur Q σ hσ)
  exact isConj_iff_eq.mp hconj ▸ hσ

include hab in
/-- Any arithmetic Frobenius at an unramified prime equals its Artin automorphism. -/
theorem artinElement_eq_of_isArithFrobAt (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) : artinElement hab 𝔭 hur = σ :=
  isArithFrobAt_eq_of_isUnramifiedAt (isArithFrobAt_artinElement hab 𝔭 hur Q) hσ

open scoped Classical in
/-- The Artin automorphism at a finite place of `K`, extended by `1` inside the excluded set `S`.

At `v ∉ S` this is the unique element of the Artin symbol of `v`, taken through the bijection
`ConjClasses.mkEquiv` between an abelian group and its conjugacy classes. The commutativity
hypothesis `hab` is what makes that bijection available, so without it there is no automorphism
here to name and only the class `artinSymbol` is defined. -/
noncomputable def artinElementAway (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)
    (v : HeightOneSpectrum (𝓞 K)) : L ≃ₐ[K] L :=
  if hv : v ∈ S then 1 else artinElement hab v.asIdeal (hur v hv)









include hab in
/-- **The Artin automorphism at `v ∉ S` is the Frobenius there.** Any arithmetic Frobenius at any
prime above `v` equals it, which is what makes the assignment `v ↦ artinElementAway hab S hur v`
well defined without a choice of prime above `v`. -/
theorem artinElementAway_eq_of_isArithFrobAt {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    artinElementAway hab S hur v = σ := by
  rw [artinElementAway, dif_neg hv]
  exact artinElement_eq_of_isArithFrobAt hab v.asIdeal (hur v hv) Q hσ

/-- **The ideal-theoretic Artin map.** The multiplicative extension of `artinElementAway` along
the unique factorization of an invertible fractional ideal, on the group of fractional ideals
with multiplicity zero at every prime of `S`. -/
noncomputable def artinHomAway : idealsAway (K := K) S →* (L ≃ₐ[K] L) :=
  letI := isMulCommutative_galoisGroup_of_commute hab
  MonoidHom.mk' (fun I ↦ ∏ᶠ v : HeightOneSpectrum (𝓞 K), artinElementAway hab S hur v ^
      FractionalIdeal.count K v ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
    fun I J ↦ by
      refine Eq.trans (finprod_congr fun v ↦ ?_)
        (finprod_mul_distrib (FractionalIdeal.hasFiniteMulSupport_zpow_count _ _)
          (FractionalIdeal.hasFiniteMulSupport_zpow_count _ _))
      rw [Subgroup.coe_mul, Units.val_mul,
        FractionalIdeal.count_mul K v (Units.ne_zero _) (Units.ne_zero _), zpow_add]

/-- **The Artin map is the product of the local Artin automorphisms, with the multiplicities of
the ideal as exponents.** The product is over all finite places of `K`, all but finitely many
factors being trivial. It is taken in the commutative structure that `hab` itself supplies, so
no bundled commutativity is asked of the caller. -/
theorem artinHomAway_apply (I : idealsAway (K := K) S) :
    artinHomAway (L := L) hab S hur I =
      letI := isMulCommutative_galoisGroup_of_commute hab
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), artinElementAway hab S hur v ^ FractionalIdeal.count K v
        ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :=
  -- The defining equation of the `MonoidHom.mk'` that `artinHomAway` is built from: the `letI`
  -- above is the same named instance term as the one in the definition, so this is `rfl`.
  (rfl)

/-- **The value of the Artin map at a prime outside `S` is its local Artin automorphism.** -/
theorem artinHomAway_apply_eq_artinElementAway (I : idealsAway (K := K) S)
    (v : HeightOneSpectrum (𝓞 K))
    (hI : ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K)) :
    artinHomAway (L := L) hab S hur I = artinElementAway hab S hur v := by
  let _ := isMulCommutative_galoisGroup_of_commute hab
  rw [artinHomAway_apply hab S hur I, finprod_eq_single _ v, hI,
    FractionalIdeal.count_self, zpow_one]
  intro w hw
  rw [hI, FractionalIdeal.count_maximal_coprime K w (Ne.symm hw), zpow_zero]

/-- **The value of the Artin map at a prime outside `S` is the Frobenius there.** -/
theorem artinHomAway_apply_prime (I : idealsAway (K := K) S) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ S)
    (hI : ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K))
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal] (σ : L ≃ₐ[K] L)
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    artinHomAway (L := L) hab S hur I = σ := by
  rw [artinHomAway_apply_eq_artinElementAway hab S hur I v hI,
    artinElementAway_eq_of_isArithFrobAt hab S hur hv Q hσ]





end ArtinHomAway

section Restrict

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
  (S : Finset (HeightOneSpectrum (𝓞 K)))
  (hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)



end Restrict

section Integral

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
  (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
  (S : Finset (HeightOneSpectrum (𝓞 K)))
  (hur : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q)

/-- **The integral Artin homomorphism.** The Artin map read on the monoid of nonzero integral
ideals divisible by no prime of `S`; this is the shape the classical statements take. -/
noncomputable def artinHomAwayIntegral : integralIdealsAway (K := K) S →* (L ≃ₐ[K] L) :=
  (artinHomAway (L := L) hab S hur).comp (integralIdealsAwayHom S)

/-- **The integral Artin homomorphism is the Artin map read through the inclusion of the integral
ideals prime to `S` into `idealsAway S`.** -/
@[simp]
theorem artinHomAwayIntegral_apply (I : integralIdealsAway (K := K) S) :
    artinHomAwayIntegral (L := L) hab S hur I =
      artinHomAway (L := L) hab S hur (integralIdealsAwayHom S I) :=
  (rfl)

/-- **The value of the integral Artin homomorphism at a prime outside `S` is the Frobenius
there.** -/
theorem artinHomAwayIntegral_apply_prime (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    (hmem : v.asIdeal ∈ integralIdealsAway (K := K) S)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal] (σ : L ≃ₐ[K] L)
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    artinHomAwayIntegral (L := L) hab S hur ⟨v.asIdeal, hmem⟩ = σ :=
  artinHomAway_apply_prime hab S hur _ v hv
    (coe_integralIdealsAwayHom S ⟨v.asIdeal, hmem⟩) Q σ hσ

end Integral

end TauCeti.NumberFieldArithmetic

end
end



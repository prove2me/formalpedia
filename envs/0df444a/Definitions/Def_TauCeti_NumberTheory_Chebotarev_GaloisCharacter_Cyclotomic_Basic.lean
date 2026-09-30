-- Prove2me | Definitions.Def_TauCeti_NumberTheory_Chebotarev_GaloisCharacter_Cyclotomic_Basic
-- name    : TauCeti_NumberTheory_Chebotarev_GaloisCharacter_Cyclotomic_Basic
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:03:16.907092+00:00
-- url     : https://prove2.me/theorems/2845f11e-f60d-496c-949d-fb0e9b332013
-- title:
--   Cyclotomic Galois characters as ray class characters
-- statement:
--   For a number field $K$ and a positive level $m$, the cyclotomic modulus has finite part $(m)$ and infinite part all real places of $K$. The Artin map for $K(\mu_m)/K$ factors as
--
--   $$
--   \operatorname{Cl}_{\mathfrak m}(K)\longrightarrow\operatorname{Gal}(K(\mu_m)/K).
--   $$
--
--   This realizes cyclotomic Galois characters as ray class characters.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/GaloisCharacter/Cyclotomic/Basic.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/GaloisCharacter/Cyclotomic/Basic.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Data_ZMod_Divisibility
import Definitions.Def_TauCeti_FieldTheory_Galois_Abelian
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_NumberTheory_NumberField_Cyclotomic_Frobenius
import Definitions.Def_TauCeti_NumberTheory_NumberField_Cyclotomic_Ramification
import Definitions.Def_TauCeti_NumberTheory_NumberField_Frobenius
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Residue
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_ArtinMap
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_NumberTheory_NumberField_TotallyPositive
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Definitions.Def_TauCeti_RingTheory_Frobenius
import Definitions.Def_TauCeti_RingTheory_Ideal_Norm_AbsNorm
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.InfiniteSum.Real
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
# Cyclotomic Galois characters as ray class characters

Let `F = K(μ_m)` be an `m`-th cyclotomic extension of a number field `K`, and let `𝔪` be the
modulus of `K` with finite part `(m)` and every real place in its infinite part. This file
provides the Artin map of the abelian extension `F / K` as a homomorphism from the ray class group
of `𝔪` to `Gal(F/K)`. It sends the ray class of a prime `𝔭 ∤ m` to the Frobenius at `𝔭`.

Composing with it, every character `χ` of `Gal(F/K)` gives a ray class character of `𝔪`, and on
the integral ideals prime to `m` the ideal weight `galoisCharacterWeight χ` of `χ` agrees with that
ray class character.

## Main definitions

* `NumberField.Chebotarev.cyclotomicModulus`: the modulus of `K` with finite part `(m)` and
  every real place in its infinite part.
* `NumberField.Chebotarev.cyclotomicArtin`: the Artin map
  `RayClassGroup (cyclotomicModulus K m) →* (F ≃ₐ[K] F)`.

## Main results

* `NumberField.Chebotarev.cyclotomicArtin_idealClass_of_isArithFrobAt`: the Artin map sends the
  ray class of a prime `𝔭 ∤ m` to the Frobenius at `𝔭`.
* `MonoidHom.galoisCharacterWeight_eq_onIdeals_cyclotomicArtin`: on the integral ideals prime to
  `m`, the ideal weight of a character `χ` of `Gal(F/K)` is the ray class character
  `χ ∘ cyclotomicArtin`.
-/

 section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

namespace NumberField.Chebotarev

open TauCeti.GlobalNumberFields TauCeti.NumberFieldArithmetic

section Modulus

variable (K : Type*) [Field K] [NumberField K] (m : ℕ) [NeZero m]

/-- **The cyclotomic modulus** of level `m`: finite part the ideal `(m)` of `𝓞 K`, and every real
place of `K` in the infinite part. The Artin map of `K(μ_m) / K` factors through its ray class
group (`cyclotomicArtin`). The definition does not unfold outside this file; use
`cyclotomicModulus_finitePart`, `mem_cyclotomicModulus_infinitePart` and
`mem_cyclotomicModulus_support_iff`. -/
noncomputable def cyclotomicModulus : Modulus K where
  finitePart := Ideal.span {(m : 𝓞 K)}
  finitePart_ne_bot := Ideal.span_singleton_eq_bot.not.mpr (NeZero.ne _)
  infinitePart := (narrowModulus K).infinitePart

/-- The finite part of the cyclotomic modulus of level `m` is the principal ideal `(m)`. -/
@[simp] theorem cyclotomicModulus_finitePart :
    (cyclotomicModulus K m).finitePart = Ideal.span {(m : 𝓞 K)} := (rfl)

/-- Every real place of `K` lies in the infinite part of the cyclotomic modulus. -/
@[simp] theorem mem_cyclotomicModulus_infinitePart (w : {w : InfinitePlace K // w.IsReal}) :
    w ∈ (cyclotomicModulus K m).infinitePart := mem_narrowModulus_infinitePart w

variable {K m}

/-- A prime lies in the support of the cyclotomic modulus exactly when it divides `m`. -/
theorem mem_cyclotomicModulus_support_iff {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ (cyclotomicModulus K m).support ↔ (m : 𝓞 K) ∈ v.asIdeal := by
  rw [Modulus.mem_support_iff, cyclotomicModulus_finitePart, Ideal.dvd_span_singleton]

/-- A height-one prime is prime to the cyclotomic modulus exactly when it does not divide `m`. -/
theorem asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff {v : HeightOneSpectrum (𝓞 K)} :
    v.asIdeal ∈ integralIdealsPrimeTo (cyclotomicModulus K m) ↔ (m : 𝓞 K) ∉ v.asIdeal :=
  Modulus.mem_integralIdealsPrimeTo.trans <|
    (Modulus.isCoprimeTo_iff.trans Ideal.isPrimeTo_iff.symm).trans <|
      Ideal.isPrimeTo_asIdeal_iff.trans mem_cyclotomicModulus_support_iff.not

end Modulus

section Auxiliary

variable {K : Type*} [Field K] [NumberField K]

-- A nonzero integer congruent to one modulo `(m)` generates an ideal prime to the cyclotomic
-- modulus.
 theorem span_singleton_mem_integralIdealsPrimeTo_cyclotomicModulus {m : ℕ} [NeZero m]
    {c : 𝓞 K} (hc0 : c ≠ 0) (hc : c - 1 ∈ Ideal.span {(m : 𝓞 K)}) :
    Ideal.span {c} ∈ integralIdealsPrimeTo (cyclotomicModulus K m) := by
  refine mem_integralIdealsAway_iff.mpr
    ⟨Ideal.span_singleton_eq_bot.not.mpr hc0, fun v hv hvc ↦ v.asIdeal.one_notMem ?_⟩
  simpa using sub_mem (Ideal.dvd_span_singleton.mp hvc) <|
    (Ideal.span_singleton_le_iff_mem _).mpr (mem_cyclotomicModulus_support_iff.mp hv) hc

end Auxiliary

section Cyclotomic

/-- For `F = K(μ_m)`, every prime of `𝓞 F` above a prime `v` of `𝓞 K` outside the support of
`cyclotomicModulus K m` (that is, with `(m : 𝓞 K) ∉ v.asIdeal`) is unramified over `𝓞 K`. -/
theorem isUnramifiedAt_of_notMem_cyclotomicModulus_support {K : Type*} [Field K] [NumberField K]
    (F : Type*) [Field F] [NumberField F] [Algebra K F] (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F]
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ (cyclotomicModulus K m).support) (Q : Ideal (𝓞 F))
    [Q.IsPrime] [Q.LiesOver v.asIdeal] : Algebra.IsUnramifiedAt (𝓞 K) Q := by
  exact IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem F m
    (mem_cyclotomicModulus_support_iff.not.mp hv) Q

variable {K : Type*} [Field K] [NumberField K] (F : Type*) [Field F] [NumberField F]
  [Algebra K F] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

-- The Artin map of `F / K` on the fractional ideals prime to `m`.
 noncomputable def cyclotomicArtinAway :
    idealsPrimeTo (cyclotomicModulus K m) →* (F ≃ₐ[K] F) :=
  artinHomAway (IsCyclotomicExtension.isMulCommutative {m} K F).is_comm.comm
    (cyclotomicModulus K m).support fun _ hv Q _ _ ↦
      isUnramifiedAt_of_notMem_cyclotomicModulus_support F m hv Q

-- The Artin map of `F / K` on the integral ideals prime to `m`.
 noncomputable def cyclotomicArtinIntegral :
    integralIdealsPrimeTo (cyclotomicModulus K m) →* (F ≃ₐ[K] F) :=
  artinHomAwayIntegral (IsCyclotomicExtension.isMulCommutative {m} K F).is_comm.comm
    (cyclotomicModulus K m).support fun _ hv Q _ _ ↦
      isUnramifiedAt_of_notMem_cyclotomicModulus_support F m hv Q

-- The integral Artin map is the fractional one read on the ideals the integral ones generate.
 theorem cyclotomicArtinIntegral_apply (I : integralIdealsPrimeTo (cyclotomicModulus K m)) :
    cyclotomicArtinIntegral F m I =
      cyclotomicArtinAway F m (integralIdealsAwayHom (cyclotomicModulus K m).support I) :=
  artinHomAwayIntegral_apply _ _ _ I

-- At a prime not dividing `m`, the integral Artin map is the Frobenius.
 theorem cyclotomicArtinIntegral_of_isArithFrobAt (v : HeightOneSpectrum (𝓞 K))
    (hv : v.asIdeal ∈ integralIdealsPrimeTo (cyclotomicModulus K m)) (Q : Ideal (𝓞 F)) [Q.IsPrime]
    [Q.LiesOver v.asIdeal] {σ : F ≃ₐ[K] F} (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    cyclotomicArtinIntegral F m ⟨v.asIdeal, hv⟩ = σ :=
  artinHomAwayIntegral_apply_prime _ _ _ v
    (mem_cyclotomicModulus_support_iff.not.mpr
      (asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff.mp hv)) hv Q σ hσ

-- The cyclotomic character of the integral Artin map is the absolute norm.
 theorem autToPow_cyclotomicArtinIntegral {ζ : F} (hζ : IsPrimitiveRoot ζ m)
    (I : integralIdealsPrimeTo (cyclotomicModulus K m)) :
    (hζ.autToPow K (cyclotomicArtinIntegral F m I) : ZMod m) =
      Ideal.absNorm (I : Ideal (𝓞 K)) := by
  let f : integralIdealsPrimeTo (cyclotomicModulus K m) →* ZMod m :=
    (Units.coeHom (ZMod m)).comp ((hζ.autToPow K).comp (cyclotomicArtinIntegral F m))
  let g : integralIdealsPrimeTo (cyclotomicModulus K m) →* ZMod m :=
    (Nat.castRingHom (ZMod m)).toMonoidHom.comp
      ((Ideal.absNorm : Ideal (𝓞 K) →*₀ ℕ).toMonoidHom.comp
        (integralIdealsPrimeTo (cyclotomicModulus K m)).subtype)
  have hfg : f = g := integralIdealsAway_hom_ext fun v hv ↦ by
    obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 F)))
    obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
    simp [f, g, cyclotomicArtinIntegral_of_isArithFrobAt F m v hv Q hσ, hσ.autToPow_eq_absNorm hζ v
      (asIdeal_mem_integralIdealsPrimeTo_cyclotomicModulus_iff.mp hv) Q]
  exact DFunLike.congr_fun hfg I

-- The Artin map of `F / K` kills the ray of the cyclotomic modulus.
 theorem ray_le_ker_cyclotomicArtinAway :
    ray (cyclotomicModulus K m) ≤ (cyclotomicArtinAway F m).ker := by
  -- For `x ≡ 1 mod 𝔪` the ideal `(x)` has absolute norm `≡ 1 mod m`, and the Artin automorphism
  -- acts on `μ_m` by the absolute norm.
  intro J hJ
  obtain ⟨x, hx, hxJ⟩ := mem_ray_iff.mp hJ
  rw [MonoidHom.mem_ker]
  have hζ := IsCyclotomicExtension.zeta_spec m K F
  refine hζ.autToPow_injective K ?_
  rw [map_one]
  rcases eq_or_ne m 1 with rfl | hm1
  · exact Subsingleton.elim _ _
  -- Write `x = a / b` with `a ≡ b ≡ 1 mod m`.
  obtain ⟨a, b, ha, hb, hab⟩ := hx.exists_sub_one_mem_and_algebraMap_eq_mul
  rw [cyclotomicModulus_finitePart] at ha hb
  have hne0 {c : 𝓞 K} (hc : c - 1 ∈ Ideal.span {(m : 𝓞 K)}) : c ≠ 0 := fun h ↦
    hm1 (Ideal.span_singleton_natCast_eq_top_iff.mp
      ((Ideal.eq_top_iff_one _).mpr (by simpa [h] using neg_mem hc)))
  have hIa := span_singleton_mem_integralIdealsPrimeTo_cyclotomicModulus (hne0 ha) ha
  have hIb := span_singleton_mem_integralIdealsPrimeTo_cyclotomicModulus (hne0 hb) hb
  -- In `idealsPrimeTo`, `(a) = (x) * (b)`.
  have hsplit : integralIdealsAwayHom _ ⟨Ideal.span {a}, hIa⟩ =
      J * integralIdealsAwayHom _ ⟨Ideal.span {b}, hIb⟩ := by
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_mul, Units.val_mul, coe_integralIdealsAwayHom, coe_integralIdealsAwayHom,
      ← hxJ, coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      hab, mul_comm]
  -- Hence the cyclotomic character of `(x)` is trivial once those of `(a)` and `(b)` agree.
  refine (mul_eq_right (b := hζ.autToPow K (cyclotomicArtinIntegral F m ⟨_, hIb⟩))).mp ?_
  rw [cyclotomicArtinIntegral_apply, ← map_mul, ← map_mul, ← hsplit, Units.ext_iff,
    ← cyclotomicArtinIntegral_apply, ← cyclotomicArtinIntegral_apply,
    autToPow_cyclotomicArtinIntegral F m hζ, autToPow_cyclotomicArtinIntegral F m hζ]
  -- They do: `a ≡ b` modulo `m`, and `N(a) = N(b) N(x)` with `N(x) > 0` as `x` is totally
  -- positive, so `N(a) N(b) = N(b) ^ 2 N(x) ≥ 0`.
  have hNab : ((Algebra.norm ℤ a : ℤ) : ℚ) = (Algebra.norm ℤ b : ℤ) * Algebra.norm ℚ (x : K) := by
    rw [Algebra.coe_norm_int, Algebra.coe_norm_int, ← map_mul]
    exact congrArg _ hab
  have hsign : (0 : ℚ) ≤ (Algebra.norm ℤ a : ℤ) * (Algebra.norm ℤ b : ℤ) := by
    rw [hNab, mul_right_comm]
    exact mul_nonneg (mul_self_nonneg _) (norm_pos_of_isTotallyPositive x.ne_zero
      (isTotallyPositive_iff.mpr fun w hw ↦
        hx.pos (mem_cyclotomicModulus_infinitePart K m ⟨w, hw⟩))).le
  exact Ideal.natCast_absNorm_span_singleton_eq_of_sub_mem (mod_cast hsign)
    (by simpa using sub_mem ha hb)

variable (K) in
/-- **The Artin map of a cyclotomic extension on the ray class group.** For `F = K(μ_m)` the
Artin map of the abelian extension `F / K` on the fractional ideals prime to `m` is trivial on the
ray of `cyclotomicModulus K m`, and so factors through its ray class group. The definition does
not unfold outside this file; it sends the ray class of a prime `𝔭 ∤ m` to the Frobenius at `𝔭`
(`cyclotomicArtin_idealClass_of_isArithFrobAt`). -/
noncomputable def cyclotomicArtin : RayClassGroup (cyclotomicModulus K m) →* (F ≃ₐ[K] F) :=
  rayClassLift (cyclotomicArtinAway F m) (ray_le_ker_cyclotomicArtinAway F m)

-- On the ray class of an integral ideal, `cyclotomicArtin` is the integral Artin map.




end Cyclotomic

end NumberField.Chebotarev

namespace MonoidHom

open TauCeti.GlobalNumberFields TauCeti.NumberFieldArithmetic NumberField.Chebotarev
open scoped IsMulCommutative

variable {K : Type*} [Field K] [NumberField K] {F : Type*} [Field F] [NumberField F]
  [Algebra K F] {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} K F] [IsGalois K F]

-- At a prime `v ∤ m`, the ideal weight of `χ` is `χ` of the Artin image of the ray class of `v`.




end MonoidHom

end
end



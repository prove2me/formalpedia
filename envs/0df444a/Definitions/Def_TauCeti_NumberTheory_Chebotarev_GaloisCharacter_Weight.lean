-- Prove2me | Definitions.Def_TauCeti_NumberTheory_Chebotarev_GaloisCharacter_Weight
-- name    : TauCeti_NumberTheory_Chebotarev_GaloisCharacter_Weight
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:51:32.585243+00:00
-- url     : https://prove2.me/theorems/501e6a23-a51f-4d4f-8fc1-2424140beabb
-- title:
--   The ideal weight of a Galois character
-- statement:
--   For a finite Galois extension $L/K$ and a multiplicative complex character $\chi$ of its Galois group, assign to a nonzero prime ideal $P$ the value
--
--   $$
--   w_\chi(P)=\begin{cases}\chi(\operatorname{Frob}_P)&P\text{ unramified},\\0&P\text{ ramified}.\end{cases}
--   $$
--
--   Extend this completely multiplicatively to nonzero ideals and set $w_\chi(0)=0$. The resulting weight is unitary on good ideals and provides the coefficients of the character Euler product.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/GaloisCharacter/Weight.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/GaloisCharacter/Weight.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_RamifiedPrimes
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_RamificationLocus
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
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
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
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
# The ideal weight of a Galois character

For a finite Galois extension `L / K` of number fields and a character `χ : Gal(L/K) →* ℂˣ`, this
file builds the *canonical ideal weight* `galoisCharacterWeight χ`: the completely multiplicative
function on the ideals of `𝓞 K` whose value at a height-one prime `𝔭` is `χ (Frob 𝔭)` when `𝔭` is
unramified in `L`, and `0` when `𝔭` ramifies. Since `Gal(L/K)` is finite those unramified values
are roots of unity, so the same weight is packaged a second time as a
`TauCeti.UnitaryIdealWeight K`.

Nothing here assumes that `L / K` is cyclotomic: the construction needs only `[IsGalois K L]`, and
the character is an arbitrary degree-one complex character of the Galois group. The Dirichlet
weight is the specialisation `L / K = ℚ(ζ_m) / ℚ`, where the cyclotomic character identifies
`Gal(ℚ(ζ_m)/ℚ)` with `(ZMod m)ˣ` and `χ` is a Dirichlet character mod `m`. Over a general base `K`
that character is still injective but need not be surjective: restriction identifies
`Gal(K(ζ_m)/K)` with the subgroup of `(ZMod m)ˣ` fixing `K ∩ ℚ(ζ_m)`, and that subgroup is all of
`(ZMod m)ˣ` exactly when `K ∩ ℚ(ζ_m) = ℚ`. The declarations are named for the generality they
actually have.

The weight is **total**, and that is a design constraint rather than a convenience: a weight
specified only away from ramification leaves its values at the bad primes unconstrained, so the
Euler product and the orthogonality identities would not pin it down. Vanishing at the ramified
primes is what makes the ramified Euler factors drop out as `(1 - 0)⁻¹ = 1`.

## Main definitions

* `MonoidHom.galoisCharacterWeight`: the weight of `χ`, packaged as a
  `TauCeti.MultiplicativeIdealWeight K`.
* `MonoidHom.galoisCharacterUnitaryWeight`: the same weight packaged as a
  `TauCeti.UnitaryIdealWeight K`, its values having modulus `1` away from the ramified primes.

## Main results

* `MonoidHom.galoisCharacterWeight_apply_of_unramified`: at an unramified height-one prime the
  weight is `χ` of the Artin symbol.
* `MonoidHom.galoisCharacterWeight_apply_eq_zero_iff`: the weight vanishes at a height-one prime
  exactly when that prime ramifies in `L`.
* `MonoidHom.badPrimes_galoisCharacterWeight`: the bad primes of the weight are exactly the
  ramified primes.
* `MonoidHom.galoisCharacterWeight_one`: the weight of the trivial character is the indicator of
  the ideals prime to the ramified primes, so its `L`-series is the Dedekind zeta function with the
  ramified Euler factors deleted.
* `MonoidHom.galoisCharacterWeight_mul`: the weight of a product of characters is the product of
  their weights.
* `MonoidHom.val_galoisCharacterUnitaryWeight`: the unitary packaging has the same underlying
  weight.
* `MonoidHom.norm_galoisCharacterWeight_le_one`: the weight of a Galois character is bounded by
  `1`.
* `MonoidHom.summable_idealTerm_galoisCharacterWeight`: the ideal series of a Galois character
  converges absolutely on `Re s > 1`.

## Implementation notes

The weight is packaged as a `TauCeti.MultiplicativeIdealWeight K` rather than as a bare function
`Ideal (𝓞 K) → ℂ`, so that the totality above is expressed in the carrier's own `badPrimes` API:
the bad primes of `χ.galoisCharacterWeight` are exactly `ramifiedPrimes K L`.

`TauCeti.UnitaryIdealWeight K` is the subtype of those multiplicative weights whose values have
modulus `1` away from the bad primes, so the unitary packaging records strictly more than the
multiplicative one and is not a replacement for it: `galoisCharacterWeight` remains the definition
everything else is stated about, and `val_galoisCharacterUnitaryWeight` is the bridge. Unitarity is
a property of the weight rather than of `χ`, so no hypothesis constrains `χ` itself to the unit
circle.

## References

Adapted from `galoisCharacterOnIdeal`, `galoisCharacterOnIdeal_mul` and
`norm_galoisCharacterOnIdeal_le_one` in `CebotarevDensity/ZetaProduct.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, following Sharifi,
*Algebraic Number Theory*, Notation 7.1.17. The factorization-product definition and the
`Multiset.map_add`/`Multiset.prod_add` multiplicativity argument are the source's; the
`MultiplicativeIdealWeight` packaging and the `artinSymbol` totalization are not the source's and
are new here. The source likewise names the construction for a general Galois character.
-/

 section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

open UniqueFactorizationMonoid
open TauCeti

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

open scoped Classical in
/-- The value of `galoisCharacterWeight χ` at a single prime: `χ (Frob 𝔭)` at an unramified
maximal `𝔭`, and `0` otherwise. -/
 noncomputable def galoisCharacterPrimeValue (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔭 : Ideal (𝓞 K)) :
    ℂ :=
  -- The unramifiedness clause is spelled out rather than named because it is, character for
  -- character, `artinSymbol`'s `hur` hypothesis: `h.2` is handed to it directly below.
  if h : 𝔭.IsMaximal ∧ ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q then
    have : 𝔭.IsMaximal := h.1
    (χ (artinSymbol (L := L) 𝔭 h.2).out : ℂ)
  else 0

open scoped Classical in
/-- The prime value extended to all ideals completely multiplicatively through the prime
factorization, with the zero ideal sent to `0`. -/
 noncomputable def galoisCharacterWeightFun (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔞 : Ideal (𝓞 K)) :
    ℂ :=
  if 𝔞 = ⊥ then 0
  else ((normalizedFactors 𝔞).map (galoisCharacterPrimeValue (L := L) χ)).prod

/-- The zero ideal has weight `0`. -/
 theorem galoisCharacterWeightFun_bot (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    galoisCharacterWeightFun (L := L) χ ⊥ = 0 := by
  simp [galoisCharacterWeightFun]

/-- Away from the zero ideal the weight is the factorization product. -/
 theorem galoisCharacterWeightFun_of_ne_bot (χ : (L ≃ₐ[K] L) →* ℂˣ) {𝔞 : Ideal (𝓞 K)}
    (h𝔞 : 𝔞 ≠ ⊥) :
    galoisCharacterWeightFun (L := L) χ 𝔞 =
      ((normalizedFactors 𝔞).map (galoisCharacterPrimeValue (L := L) χ)).prod := by
  simp [galoisCharacterWeightFun, h𝔞]

/-- The unit ideal has weight `1`. -/
 theorem galoisCharacterWeightFun_top (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    galoisCharacterWeightFun (L := L) χ ⊤ = 1 := by
  rw [galoisCharacterWeightFun_of_ne_bot χ top_ne_bot, ← Ideal.one_eq_top,
    normalizedFactors_one, Multiset.map_zero, Multiset.prod_zero]

/-- **Complete multiplicativity.** The weight of a product of ideals is the product of the
weights. -/
 theorem galoisCharacterWeightFun_mul (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔞 𝔟 : Ideal (𝓞 K)) :
    galoisCharacterWeightFun (L := L) χ (𝔞 * 𝔟) =
      galoisCharacterWeightFun (L := L) χ 𝔞 * galoisCharacterWeightFun (L := L) χ 𝔟 := by
  -- Both degenerate cases collapse: `⊥ * 𝔟 = ⊥` and `𝔞 * ⊥ = ⊥`, so each side is `0`.
  rcases eq_or_ne 𝔞 ⊥ with rfl | h𝔞
  · simp [galoisCharacterWeightFun_bot]
  rcases eq_or_ne 𝔟 ⊥ with rfl | h𝔟
  · simp [galoisCharacterWeightFun_bot]
  -- `Ideal.mul_eq_bot`, not `mul_ne_zero`: the latter produces `𝔞 * 𝔟 ≠ 0`, and although `0` and
  -- `⊥` are definitionally equal for ideals they are not syntactically equal, so `rw` cannot
  -- match it against the `⊥` in the definition.
  have hab : 𝔞 * 𝔟 ≠ ⊥ := fun h ↦ (Ideal.mul_eq_bot.mp h).elim h𝔞 h𝔟
  rw [galoisCharacterWeightFun_of_ne_bot χ hab, galoisCharacterWeightFun_of_ne_bot χ h𝔞,
    galoisCharacterWeightFun_of_ne_bot χ h𝔟, normalizedFactors_mul h𝔞 h𝔟,
    Multiset.map_add, Multiset.prod_add]

/-- On a height-one prime the weight is just the single prime value. -/
 theorem galoisCharacterWeightFun_heightOne (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    galoisCharacterWeightFun (L := L) χ 𝔭.asIdeal =
      galoisCharacterPrimeValue (L := L) χ 𝔭.asIdeal := by
  -- The factorization of a prime ideal is the one-element multiset.
  simp only [galoisCharacterWeightFun_of_ne_bot χ 𝔭.ne_bot,
    normalizedFactors_irreducible 𝔭.irreducible, normalize_eq, Multiset.map_singleton,
    Multiset.prod_singleton]

/-- The weight vanishes at a height-one prime exactly when that prime ramifies in `L`. -/
 theorem galoisCharacterWeightFun_heightOne_eq_zero_iff (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    galoisCharacterWeightFun (L := L) χ 𝔭.asIdeal = 0 ↔ 𝔭 ∈ ramifiedPrimes K L := by
  rw [galoisCharacterWeightFun_heightOne, galoisCharacterPrimeValue, mem_ramifiedPrimes_iff]
  -- A height-one prime is maximal, so the `dite` condition reduces to unramifiedness.
  split_ifs with h
  · exact iff_of_false (Units.ne_zero _) (not_not_intro h.2)
  · exact iff_of_true rfl fun hc ↦ h ⟨𝔭.isMaximal, hc⟩

end NumberField.Chebotarev

open NumberField NumberField.Chebotarev

namespace MonoidHom

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **The ideal weight of a Galois character** `χ`, packaged as a `MultiplicativeIdealWeight`. On a
height-one prime it is `χ (Frob 𝔭)` at the unramified primes and `0` at the ramified ones, extended
to all ideals completely multiplicatively through the prime factorization. -/
noncomputable def galoisCharacterWeight (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    TauCeti.MultiplicativeIdealWeight K where
  toMonoidWithZeroHom :=
    { toFun := galoisCharacterWeightFun (L := L) χ
      map_zero' := galoisCharacterWeightFun_bot χ
      map_one' := by simpa using galoisCharacterWeightFun_top (L := L) χ
      map_mul' := galoisCharacterWeightFun_mul χ }
  -- The vanishing set is exactly `ramifiedPrimes K L`, which is already a `Finset`.
  finite_setOf_apply_eq_zero := (ramifiedPrimes K L).finite_toSet.subset fun 𝔭 h𝔭 ↦
    (galoisCharacterWeightFun_heightOne_eq_zero_iff χ 𝔭).mp h𝔭

/-- Defining equation of `galoisCharacterWeight`. -/
 theorem galoisCharacterWeight_apply (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔞 : Ideal (𝓞 K)) :
    galoisCharacterWeight (L := L) χ 𝔞 = galoisCharacterWeightFun (L := L) χ 𝔞 := (rfl)

/-- **Value at an unramified prime.** At a height-one prime unramified in `L` the weight is `χ` of
the Artin symbol; together with the vanishing at ramified primes and complete multiplicativity this
determines the weight. -/
theorem galoisCharacterWeight_apply_of_unramified (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (𝔭 : HeightOneSpectrum (𝓞 K))
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
    galoisCharacterWeight (L := L) χ 𝔭.asIdeal =
      (χ (artinSymbol (L := L) 𝔭.asIdeal hur).out : ℂ) := by
  rw [galoisCharacterWeight_apply, galoisCharacterWeightFun_heightOne, galoisCharacterPrimeValue]
  -- The `dite` condition holds: a height-one prime is maximal, and `hur` is its second half.
  -- Both branches close by proof irrelevance in the unramifiedness and maximality proofs.
  split_ifs with h
  · rfl
  · exact absurd ⟨𝔭.isMaximal, hur⟩ h

/-- The weight vanishes at a height-one prime exactly when that prime ramifies in `L`. This is what
makes the weight *total*: the bad primes are not left unconstrained, they are pinned to `0`. -/
@[simp]
theorem galoisCharacterWeight_apply_eq_zero_iff (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    galoisCharacterWeight (L := L) χ 𝔭.asIdeal = 0 ↔ 𝔭 ∈ ramifiedPrimes K L := by
  rw [galoisCharacterWeight_apply]
  exact galoisCharacterWeightFun_heightOne_eq_zero_iff χ 𝔭

/-- The bad primes of the weight are exactly the ramified primes. -/
@[simp]
theorem badPrimes_galoisCharacterWeight (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    (galoisCharacterWeight (L := L) χ).badPrimes = ↑(ramifiedPrimes K L) := by
  ext 𝔭
  simpa only [TauCeti.MultiplicativeIdealWeight.mem_badPrimes, Finset.mem_coe] using
    galoisCharacterWeight_apply_eq_zero_iff χ 𝔭





/-- **The weight of a Galois character is unitary.** Its values have modulus `1` at every
unramified prime, and `0` at the ramified ones — which is exactly the `UnitaryIdealWeight`
contract, `badPrimes` being the ramified set by `badPrimes_galoisCharacterWeight`.

The underlying weight is `galoisCharacterWeight χ` itself, by
`val_galoisCharacterUnitaryWeight`. No hypothesis beyond multiplicativity is placed on `χ`; in
particular it is not assumed to take values in the unit circle. -/
noncomputable def galoisCharacterUnitaryWeight (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    TauCeti.UnitaryIdealWeight K :=
  TauCeti.UnitaryIdealWeight.ofPowEqOne (galoisCharacterWeight (L := L) χ)
    (n := Nat.card (L ≃ₐ[K] L)) Nat.card_pos.ne' (fun 𝔭 h𝔭 ↦ by
      have hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
          Algebra.IsUnramifiedAt (𝓞 K) Q := by
        by_contra h
        exact h𝔭 (by simpa [badPrimes_galoisCharacterWeight] using
          (NumberField.Chebotarev.mem_ramifiedPrimes_iff (L := L) 𝔭).mpr h)
      rw [galoisCharacterWeight_apply_of_unramified χ 𝔭 hur, ← Units.val_pow_eq_pow_val,
        ← map_pow, pow_card_eq_one', map_one, Units.val_one])







end MonoidHom

end
end



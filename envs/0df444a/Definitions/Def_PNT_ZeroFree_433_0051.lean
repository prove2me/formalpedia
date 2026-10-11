-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0051
-- name    : PNT_ZeroFree_433_0051
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T15:15:28.226868+00:00
-- url     : https://prove2.me/theorems/3391aa5c-b42f-410e-8bf6-7dd08901161f
-- title:
--   Zero-free region foundations: QuadraticSieve.CoefficientCancellation [0051]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.CoefficientCancellation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CoefficientCancellation.lean#L77-L681

import Definitions.Def_PNT_ZeroFree_433_0050

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CoefficientCancellation.lean#L77-L681
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.CoefficientCancellation
section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

namespace MixedCrossSeparation
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion

theorem norm_localCoefficient (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    ‖localCoefficient p hp hg‖ = 1 := by
  rw [localCoefficient, norm_mul, norm_star, norm_angularFactor p hp,
    norm_localGauss p hp hg hc 2 (by decide) (by decide), one_mul]

theorem local_coefficient_cancel (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (hpr : lambda ^ 2 ∣ p - 1) :
    localCoefficient p hp hg * convertedLocal p hp hg false = localG p hp hg ∧
      star (localCoefficient p hp hg) * convertedLocal p hp hg true =
        canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
          star (localG p hp hg) := by
  have hA : localCoefficient p hp hg * star (localCoefficient p hp hg) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', norm_localCoefficient p hp hg hc]
    norm_num
  have hG : localG p hp hg * star (localG p hp hg) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', norm_localG p hp hg hc hpr]
    norm_num
  have hGn : localG p hp hg ≠ 0 := by
    intro h
    simp [h] at hG
  have hGsn := star_ne_zero.mpr hGn
  constructor
  · simp only [convertedLocal, Bool.false_eq_true, ↓reduceIte]
    rw [← mul_div_assoc]
    apply (div_eq_iff hGsn).mpr
    rw [hA, hG]
  · simp only [convertedLocal, ↓reduceIte]
    rw [← mul_div_assoc]
    apply (div_eq_iff hGn).mpr
    calc
      _ = canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
          (localCoefficient p hp hg * star (localCoefficient p hp hg)) := by ring
      _ = _ := by
        rw [hA]
        calc
          _ = canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
              (localG p hp hg * star (localG p hp hg)) := by rw [hG]
          _ = _ := by ring

theorem canonicalProductG_crt {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) :
    canonicalProductG p hp hcop hg = canonicalCrossFactor p hg ^ 3 *
      ∏ i, localG (p i) (hp i) (hg i) := by
  rw [canonicalProductG, canonicalProductGauss_constant_power p hp hcop hg 3 (by decide)]
  change (∏ i, canonicalSextic (Ideal.span {p i}) (hg i)
      (Ideal.Quotient.mk (Ideal.span {p i}) (4 : O)))⁻¹ *
      (canonicalCrossFactor p hg ^ 3 * ∏ i, localGauss (p i) (hp i) (hg i) 3) = _
  simp only [localG, breveLocalG, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  change (∏ i, canonicalSextic (Ideal.span {p i}) (hg i)
      (Ideal.Quotient.mk (Ideal.span {p i}) (4 : O)))⁻¹ *
      (canonicalCrossFactor p hg ^ 3 * ∏ i, localGauss (p i) (hp i) (hg i) 3) =
    canonicalCrossFactor p hg ^ 3 *
      ((∏ i, canonicalSextic (Ideal.span {p i}) (hg i)
        (Ideal.Quotient.mk (Ideal.span {p i}) (4 : O)))⁻¹ *
        ∏ i, localGauss (p i) (hp i) (hg i) 3)
  ring

theorem convertedColumnBlock_univ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (b : Bool) :
    convertedColumnBlock p hp hg Finset.univ b =
      canonicalCrossFactor p hg ^ (if b then 5 else 1) *
        ∏ i, convertedLocal (p i) (hp i) (hg i) b := by
  simp only [convertedColumnBlock, Finset.prod_mul_distrib, ← Finset.prod_pow,
    canonicalCrossFactor, crossSymbol]
  congr 2
  funext i
  congr 1
  ext k
  simp

theorem coefficient_cancel_univ_false {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductCoefficient p hp hcop hg * convertedColumnBlock p hp hg Finset.univ false =
      canonicalProductG p hp hcop hg := by
  rw [canonicalProductCoefficient_crt, convertedColumnBlock_univ, canonicalProductG_crt]
  change (canonicalCrossFactor p hg ^ 2 * ∏ i, localCoefficient (p i) (hp i) (hg i)) *
      (canonicalCrossFactor p hg ^ 1 * ∏ i, convertedLocal (p i) (hp i) (hg i) false) = _
  calc
    _ = canonicalCrossFactor p hg ^ 3 * ∏ i,
        localCoefficient (p i) (hp i) (hg i) * convertedLocal (p i) (hp i) (hg i) false := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by
      congr 1
      exact Finset.prod_congr rfl (fun i _ => (local_coefficient_cancel (p i) (hp i) (hg i) (hc i) (hpr i)).1)

theorem coefficient_cancel_univ_true {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) :
    star (canonicalProductCoefficient p hp hcop hg) * convertedColumnBlock p hp hg Finset.univ true =
      (∏ i, canonicalSextic (Ideal.span {p i}) (hg i)
        (Ideal.Quotient.mk (Ideal.span {p i}) (-1 : O))) * star (canonicalProductG p hp hcop hg) := by
  let C := canonicalCrossFactor p hg
  have hC6 : C ^ 6 = 1 := canonicalCrossFactor_pow_six p hcop hg
  have hCn : ‖C‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hC6 (by decide)
  have hCC : C * star C = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', hCn]
    norm_num
  have hC3 : star C ^ 3 = C ^ 3 := by
    have hh : (C ^ 3) ^ 2 = 1 := by simpa only [← pow_mul] using hC6
    rw [← star_pow]
    rcases (sq_eq_one_iff).mp hh with h | h <;> simp [h]
  rw [canonicalProductCoefficient_crt, convertedColumnBlock_univ, canonicalProductG_crt]
  change star (C ^ 2 * ∏ i, localCoefficient (p i) (hp i) (hg i)) *
      (C ^ 5 * ∏ i, convertedLocal (p i) (hp i) (hg i) true) =
        _ * star (C ^ 3 * ∏ i, localG (p i) (hp i) (hg i))
  simp only [star_mul, star_pow, star_prod, hC3]
  calc
    _ = (C * star C) ^ 2 * C ^ 3 * ∏ i,
        star (localCoefficient (p i) (hp i) (hg i)) * convertedLocal (p i) (hp i) (hg i) true := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = C ^ 3 * ∏ i,
        canonicalSextic (Ideal.span {p i}) (hg i)
          (Ideal.Quotient.mk (Ideal.span {p i}) (-1 : O)) * star (localG (p i) (hp i) (hg i)) := by
      rw [hCC, one_pow, one_mul]
      congr 1
      exact Finset.prod_congr rfl (fun i _ => (local_coefficient_cancel (p i) (hp i) (hg i) (hc i) (hpr i)).2)
    _ = _ := by rw [Finset.prod_mul_distrib]; ring

theorem columnPrimeCoprime {ι : Type*} (p : ι → O)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (S : Finset ι) :
    Pairwise (Function.onFun IsCoprime (fun i : S => Ideal.span {p i.val})) := by
  intro i j hij
  exact hcop (fun h => hij (Subtype.ext h))

def columnCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) : ℂ :=
  canonicalProductCoefficient (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val)

def columnG {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) : ℂ :=
  canonicalProductG (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val)

theorem convertedColumnBlock_subtype {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (b : Bool) :
    convertedColumnBlock (fun i : S => p i.val) (fun i => hp i.val)
      (fun i => hg i.val) Finset.univ b = convertedColumnBlock p hp hg S b := by
  have h := convertedColumnBlock_image p hp hg (Subtype.val : S → ι)
    Subtype.val_injective Finset.univ b
  have he : (Finset.univ : Finset S).image Subtype.val = S := by ext; simp
  simpa only [he] using h

theorem columnCoefficient_cancel_false {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    columnCoefficient p hp hcop hg S * convertedColumnBlock p hp hg S false =
      columnG p hp hcop hg S := by
  have h := coefficient_cancel_univ_false (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => hc i.val) (fun i => hpr i.val)
  rw [convertedColumnBlock_subtype] at h
  exact h

theorem columnCoefficient_cancel_true {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    star (columnCoefficient p hp hcop hg S) * convertedColumnBlock p hp hg S true =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) *
        star (columnG p hp hcop hg S) := by
  have h := coefficient_cancel_univ_true (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => hc i.val) (fun i => hpr i.val)
  have hprod : (∏ i : S, canonicalSextic (Ideal.span {p i.val}) (hg i.val)
      (Ideal.Quotient.mk (Ideal.span {p i.val}) (-1 : O))) =
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) := by
    simpa only [finiteSquarefreeRow] using
      (Finset.prod_coe_sort S (fun i => canonicalSextic (Ideal.span {p i}) (hg i)
        (Ideal.Quotient.mk (Ideal.span {p i}) (-1 : O))))
  rw [convertedColumnBlock_subtype, hprod] at h
  exact h

end MixedCrossSeparation

open scoped BigOperators Classical SchwartzMap ContDiff
namespace FirstCauchyArithmetic
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open MixedCrossSeparation GaussGeneratorTransport ConcretePrimeRowBridge EisensteinSchwartzPoisson

def firstPassColumnMinus {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1)) *
    columnG p hp hcop hg S * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d * C S

def firstPassColumnPlus {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  columnG p hp hcop hg S * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d * C S

theorem norm_columnG
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    ‖columnG p hp hcop hg S‖ = 1 :=
  norm_canonicalProductG (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => hc i.val) (fun i => hpr i.val)

theorem norm_firstPassColumnMinus_le
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (C : Finset ι → ℂ) (d : O) (S : Finset ι) :
    ‖firstPassColumnMinus p hp hcop hg C d S‖ ≤ ‖C S‖ := by
  simp only [firstPassColumnMinus, norm_mul, norm_star, norm_columnG p hp hcop hg hc hpr]
  calc
    _ ≤ 1 * 1 * 1 * ‖C S‖ := by
      gcongr
      · exact finiteSquarefreeRow_norm_le_one (fun i => Ideal.span {p i}) hg S (-1)
      · exact finiteSquarefreeRow_norm_le_one (fun i => Ideal.span {p i}) hg S d
    _ = _ := by ring

theorem norm_firstPassColumnPlus_le
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (C : Finset ι → ℂ) (d : O) (S : Finset ι) :
    ‖firstPassColumnPlus p hp hcop hg C d S‖ ≤ ‖C S‖ := by
  simp only [firstPassColumnPlus, norm_mul, norm_columnG p hp hcop hg hc hpr, one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (finiteSquarefreeRow_norm_le_one (fun i => Ideal.span {p i}) hg S d)

theorem a_weighted_converted_pair
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (hd : Disjoint S T) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let row := finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T)
    star (columnCoefficient p hp hcop hg S * C₁ S) *
      (columnCoefficient p hp hcop hg T * C₂ T) *
      (supportMobius P S * supportMobius P T * activeConvertedGauss p hp hg S T) *
        (row d * star (row h)) =
    quadraticCrossPhase p hg S T *
      star (supportMobius P S * firstPassColumnMinus p hp hcop hg C₁ d S *
        star (finiteSquarefreeRow P hg S h)) *
      (supportMobius P T * firstPassColumnPlus p hp hcop hg C₂ d T *
        star (finiteSquarefreeRow P hg T h)) := by
  dsimp only
  rw [activeConvertedGauss_eq_columnBlocks p hp hg hpr S T,
    active_dual_row_factorization (fun i => Ideal.span {p i}) hg S T d h,
    Finset.sdiff_eq_self_of_disjoint hd, Finset.sdiff_eq_self_of_disjoint hd.symm]
  have hminus := columnCoefficient_cancel_true p hp hcop hg hc hpr S
  have hplus := columnCoefficient_cancel_false p hp hcop hg hc hpr T
  simp only [firstPassColumnMinus, firstPassColumnPlus, star_mul, star_star,
    star_supportMobius]
  calc
    _ = (star (columnCoefficient p hp hcop hg S) * convertedColumnBlock p hp hg S true) *
      (columnCoefficient p hp hcop hg T * convertedColumnBlock p hp hg T false) *
      (star (C₁ S) * C₂ T * supportMobius (fun i => Ideal.span {p i}) S *
        supportMobius (fun i => Ideal.span {p i}) T * quadraticCrossPhase p hg S T *
        (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S h *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d)) *
        (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T d *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T h))) := by ring
    _ = _ := by rw [hminus, hplus]; ring

theorem active_productGauss_eq_mobius_converted
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    let q : activeSupport S T → O := fun i => p i.val
    canonicalProductGauss q (fun i => hp i.val)
      (activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T)
      (fun i => hg i.val) (activeExponent S T) =
    supportMobius (fun i => Ideal.span {p i}) S *
      supportMobius (fun i => Ideal.span {p i}) T * activeConvertedGauss p hp hg S T := by
  dsimp only
  let : DecidableEq (activeSupport S T) := fun a b => Classical.propDecidable (a = b)
  let q : activeSupport S T → O := fun i => p i.val
  let hq := activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T
  have he : activeExponent S T =
      (fun i : activeSupport S T => if decide (i.val ∈ S \ T) then 5 else 1) := by
    funext i
    simp only [activeExponent, decide_eq_true_eq]
  have h' : (supportMobius (fun i => Ideal.span {p i}) S *
      supportMobius (fun i => Ideal.span {p i}) T) *
      canonicalProductGauss q (fun i => hp i.val) hq (fun i => hg i.val)
        (activeExponent S T) = activeConvertedGauss p hp hg S T := by
    rw [supportMobius, supportMobius, pair_moebius_eq_active p hinj S T]
    unfold activeConvertedGauss
    rw [he]
    exact moebius_mixed_gauss_conversion q (fun i => hp i.val) hq (fun i => hg i.val)
      (fun i => hc i.val) (fun i => hpr i.val) (fun i => decide (i.val ∈ S \ T))
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hs := supportMobius_sq (fun i => Ideal.span {p i}) hprime hinj S
  have ht := supportMobius_sq (fun i => Ideal.span {p i}) hprime hinj T
  calc
    _ = (supportMobius (fun i => Ideal.span {p i}) S * supportMobius (fun i => Ideal.span {p i}) S) *
      (supportMobius (fun i => Ideal.span {p i}) T * supportMobius (fun i => Ideal.span {p i}) T) *
      canonicalProductGauss q (fun i => hp i.val) hq (fun i => hg i.val) (activeExponent S T) := by
        rw [hs, ht]; ring
    _ = _ := by rw [← h']; ring

def activeGaussRowFactor
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (d h : O) : ℂ :=
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let row := finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T)
  canonicalProductGauss (fun i : activeSupport S T => p i.val) (fun i => hp i.val)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val) (activeExponent S T) *
      (row d * star (row h))

theorem disjoint_pair_poisson_arithmetic
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S T : Finset ι) (hd : Disjoint S T)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let n := ∏ i : activeSupport S T, p i.val
    (∑' z : O, (star (finiteSquarefreeRow P hg S z) * finiteSquarefreeRow P hg T z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
    ((scale : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
      ∑' h : O, paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding n‖ ^ 2) *
        activeGaussRowFactor p hp hinj hg S T 1 h := by
  dsimp only
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let q : activeSupport S T → O := fun i => p i.val
  let hq := activePrimes_pairwise_isCoprime P hinj S T
  let row := finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T)
  let G := canonicalProductGauss q (fun i => hp i.val) hq (fun i => hg i.val) (activeExponent S T)
  have hpz (z : O) : star (finiteSquarefreeRow P hg S z) * finiteSquarefreeRow P hg T z = row z := by
    rw [finiteSquarefreeRow_pair_activeSupport]
    simp [Finset.disjoint_iff_inter_eq_empty.mp hd, rowCoprimeMask, row]
  have hrow1 : row 1 = 1 := by simp [row, finiteSexticRow]
  have ht := canonical_radial_poisson_product q (fun i => hp i.val) hq (fun i => hg i.val)
    (fun i => hc i.val) (activeExponent S T) (activeExponent_ne_zero S T)
    (activeExponent_lt_six S T) W scale hscale
  have hseries : (∑' h : O,
      paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, q i)‖ ^ 2) *
        activeGaussRowFactor p hp hinj hg S T 1 h) =
      G * ∑' h : O, star (row h) *
        paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, q i)‖ ^ 2) := by
    calc
      _ = ∑' h : O, G * (star (row h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, q i)‖ ^ 2)) := by
        apply tsum_congr
        intro h
        change _ * (G * (row 1 * star (row h))) = _
        rw [hrow1]
        ring
      _ = _ := tsum_mul_left
  rw [hseries]
  calc
    _ = ∑' z : O, row z * W (‖eisEmbedding z‖ ^ 2 / scale) := by
      apply tsum_congr
      intro z
      rw [hpz]
    _ = ((scale : ℂ) * G / (‖eisEmbedding (∏ i, q i)‖ : ℂ)) *
        ∑' h : O, star (row h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (∏ i, q i)‖ ^ 2) := ht
    _ = _ := by ring

theorem a_weighted_activeGaussRowFactor
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (hd : Disjoint S T) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    star (columnCoefficient p hp hcop hg S * C₁ S) *
      (columnCoefficient p hp hcop hg T * C₂ T) * activeGaussRowFactor p hp hinj hg S T d h =
    quadraticCrossPhase p hg S T *
      star (supportMobius P S * firstPassColumnMinus p hp hcop hg C₁ d S *
        star (finiteSquarefreeRow P hg S h)) *
      (supportMobius P T * firstPassColumnPlus p hp hcop hg C₂ d T *
        star (finiteSquarefreeRow P hg T h)) := by
  dsimp only
  unfold activeGaussRowFactor
  dsimp only
  rw [active_productGauss_eq_mobius_converted p hp hinj hg hc hpr S T]
  simpa only [mul_assoc] using a_weighted_converted_pair p hp hcop hg hc hpr S T hd C₁ C₂ d h

theorem a_weighted_pair_sum_to_second_poisson_rows
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (B : Finset ι) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let D₁ := firstPassColumnMinus p hp hcop hg C₁ d
    let D₂ := firstPassColumnPlus p hp hcop hg C₂ d
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then
        star (columnCoefficient p hp hcop hg S * C₁ S) *
          (columnCoefficient p hp hcop hg T * C₂ T) *
            activeGaussRowFactor p hp hinj hg S T d h else 0) =
    ∑ r : RayFourExpansion.RayCharacter × RayFourExpansion.RayCharacter,
      RayFourExpansion.crossCoeff r.1 r.2 *
      ∑ D ∈ B.powerset,
        (supportMobius P D * rowCoprimeMask P D h * supportRay p r.1 D * supportRay p r.2 D) *
        star (conjugateIdealRowSum (supportIdealFamily P (B \ D))
          (supportIdealFamily_pos P (B \ D)) (supportIdealFamily_good P hg (B \ D))
          (fun I => star (supportRay p r.1 (recoveredSupport P (B \ D) I)) *
            D₁ (D ∪ recoveredSupport P (B \ D) I)) h) *
        conjugateIdealRowSum (supportIdealFamily P (B \ D))
          (supportIdealFamily_pos P (B \ D)) (supportIdealFamily_good P hg (B \ D))
          (fun I => supportRay p r.2 (recoveredSupport P (B \ D) I) *
            D₂ (D ∪ recoveredSupport P (B \ D) I)) h := by
  dsimp only
  rw [← quadratic_phase_reindex_to_ideal_rows p hp hinj hg hc B
    (firstPassColumnMinus p hp hcop hg C₁ d) (firstPassColumnPlus p hp hcop hg C₂ d) h]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · rw [if_pos hd, if_pos hd]
    exact a_weighted_activeGaussRowFactor p hp hinj hcop hg hc hpr S T hd C₁ C₂ d h
  · rw [if_neg hd, if_neg hd]

end FirstCauchyArithmetic

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def pvSeminorms : Finset (ℕ × ℕ) :=
  Classical.choose paperRadialFourier_nonzero_lattice_uniform

def pvConstant : ℝ :=
  Classical.choose (Classical.choose_spec paperRadialFourier_nonzero_lattice_uniform)

theorem pvConstant_pos : 0 < pvConstant :=
  (Classical.choose_spec
    (Classical.choose_spec paperRadialFourier_nonzero_lattice_uniform)).1

def pvControl (W : 𝓢(ℝ, ℂ)) : ℝ :=
  pvConstant * pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ) W

theorem pvControl_nonneg (W : 𝓢(ℝ, ℂ)) : 0 ≤ pvControl W :=
  mul_nonneg pvConstant_pos.le (apply_nonneg _ _)

theorem pv_lattice_bound (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    t * (∑' h : {h : O // h ≠ 0},
      ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖) ≤ pvControl W :=
  (Classical.choose_spec
    (Classical.choose_spec paperRadialFourier_nonzero_lattice_uniform)).2 W t ht

theorem norm_finite_character_le_one {R : Type*} [CommRing R] [Fintype R]
    (χ : MulChar R ℂ) (r : R) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simpa only [MulChar.coe_equivToUnitHom] using
      (Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)).le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    exact zero_le_one

theorem finiteSexticRow_norm_le_one {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (j : ι → ℕ) (a : O) :
    ‖finiteSexticRow P hg j a‖ ≤ 1 := by
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  rw [finiteSexticRow, norm_prod]
  calc
    _ ≤ ∏ i : ι, (1 : ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun i _ => norm_finite_character_le_one
        (canonicalSextic (P i) (hg i) ^ j i) _)
    _ = 1 := by simp

theorem canonical_polya_vinogradov {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, lambda ∉ P i) (hc : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, finiteSexticRow P hg j z * W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      pvControl W * ‖eisEmbedding (finitePrimeModulus P)‖ := by
  let c := finitePrimeModulus P
  let q := ‖eisEmbedding c‖
  have hq : 0 < q := norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P))
  let t := M / q ^ 2
  have ht : 0 < t := div_pos hM (sq_pos_of_pos hq)
  let F : O → ℂ := fun h => star (finiteSexticRow P hg j h) *
    paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)
  have hF (h : O) : ‖F h‖ ≤ ‖paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)‖ := by
    dsimp only [F]
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (finiteSexticRow_norm_le_one P hg j h)
  have hs := paperRadialFourier_lattice_summable_norm W t ht
  have hFs : Summable (fun h : O => ‖F h‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF hs
  have hzero : F 0 = 0 := by simp only [F, finiteSexticRow_zero, star_zero, zero_mul]
  have heq : (∑' h : O, F h) = ∑' h : {h : O // h ≠ 0}, F h := by
    symm
    apply tsum_subtype_eq_of_support_subset
    intro h hh
      hz
    subst h
    exact hh hzero
  have hn : ‖∑' h : O, F h‖ ≤
      ∑' h : {h : O // h ≠ 0}, ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖ := by
    rw [heq]
    exact (norm_tsum_le_tsum_norm (hFs.subtype _)).trans
      ((hFs.subtype _).tsum_le_tsum (fun h => hF h) (hs.subtype _))
  have hbound : t * ‖∑' h : O, F h‖ ≤ pvControl W :=
    (mul_le_mul_of_nonneg_left hn ht.le).trans (pv_lattice_bound W t ht)
  rw [canonical_radial_poisson_normalized P hcop hg hc j hj0 hj6 W M hM]
  have hargs (h : O) : M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2 =
      t * ‖eisEmbedding h‖ ^ 2 := by dsimp [t, q]; ring
  change ‖((M : ℂ) * canonicalNormalizedGauss P hcop hg j / (q : ℂ)) *
    ∑' h : O, star (finiteSexticRow P hg j h) *
      paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)‖ ≤ _
  simp_rw [hargs]
  change ‖((M : ℂ) * canonicalNormalizedGauss P hcop hg j / (q : ℂ)) * ∑' h : O, F h‖ ≤ _
  rw [norm_mul, norm_div, norm_mul, norm_canonicalNormalizedGauss P hcop hg hc j hj0 hj6,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  change M / q * ‖∑' h : O, F h‖ ≤ pvControl W * q
  calc
    _ = q * (t * ‖∑' h : O, F h‖) := by dsimp [t]; field_simp
    _ ≤ q * pvControl W := mul_le_mul_of_nonneg_left hbound hq.le
    _ = _ := mul_comm _ _

theorem norm_ideal_moebius_le_one (I : Ideal O) :
    ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ ≤ 1 := by
  unfold UniqueFactorizationMonoid.moebius
  split_ifs <;> simp

theorem canonical_masked_polya_vinogradov
    {α ι : Type*} [DecidableEq α] [Fintype ι] [Nonempty ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset α) (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hg : ∀ i, lambda ∉ Q i) (hc : ∀ i, ringChar (O ⧸ Q i) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, rowCoprimeMask P S z * finiteSexticRow Q hg j z *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      (2 : ℝ) ^ S.card * (pvControl W * ‖eisEmbedding (finitePrimeModulus Q)‖) := by
  rw [canonical_masked_radial_dilations P hinj S Q hcop hg j W M hM]
  calc
    _ ≤ ∑ E ∈ S.powerset, ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        finiteSexticRow Q hg j (primeSubsetGenerator P E) *
        ∑' z : O, finiteSexticRow Q hg j z *
          W (‖eisEmbedding z‖ ^ 2 / (M / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _E ∈ S.powerset, pvControl W * ‖eisEmbedding (finitePrimeModulus Q)‖ := by
      apply Finset.sum_le_sum
      intro E hE
      rw [norm_mul, norm_mul]
      have hp := canonical_polya_vinogradov Q hcop hg hc j hj0 hj6 W _
        (primeSubset_reducedScale_pos P E hM)
      have hmul : ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ)‖ *
          ‖finiteSexticRow Q hg j (primeSubsetGenerator P E)‖ ≤ 1 := by
        calc
          _ ≤ 1 * 1 := mul_le_mul (norm_ideal_moebius_le_one _)
            (finiteSexticRow_norm_le_one Q hg j _) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul _
      exact (mul_le_of_le_one_left (norm_nonneg _) hmul).trans hp
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

end QuadraticInitialBound

end

end OAI

end



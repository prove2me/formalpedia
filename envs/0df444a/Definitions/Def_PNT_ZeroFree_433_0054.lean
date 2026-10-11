-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0054
-- name    : PNT_ZeroFree_433_0054
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T15:36:00.016582+00:00
-- url     : https://prove2.me/theorems/cda57b2a-44bb-437b-bbbc-efc8d7214e81
-- title:
--   Zero-free region foundations: Arithmetic.SquarefreeDivisors [0054]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Arithmetic.SquarefreeDivisors
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Arithmetic/SquarefreeDivisors.lean#L374-L670

import Definitions.Def_PNT_ZeroFree_433_0054_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Arithmetic/SquarefreeDivisors.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

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

namespace SquarefreeDivisorBound
open scoped BigOperators Classical
open Filter IdealMobiusDivisorSum


open DescentWeightedCauchy


end SquarefreeDivisorBound

namespace VerticalContourShift
open MeasureTheory Filter Set
open scoped Topology


end VerticalContourShift

open scoped BigOperators Classical
namespace FirstPassCubeLabels

open ActualEisensteinCubic


section Rows
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)


include hg


def localFactor (side parityBit ε₁ ε₂ : Bool) (a : O) : ℂ :=
  rowCoprimeMask P S a *
    finiteSquarefreeRow P hg S a ^ (4 * bit (if side then ε₂ else ε₁)) *
    finiteSquarefreeRow P hg S a ^ crtExponent side parityBit ε₁ ε₂ *
    finiteSquarefreeRow P hg S a ^ dilationExponent parityBit ε₁ ε₂

theorem localFactor_eq (side parityBit ε₁ ε₂ : Bool) (a : O) :
    localFactor P hg S side parityBit ε₁ ε₂ a =
      if retained parityBit ε₁ ε₂ then finiteSquarefreeRow P hg S a ^ 4
      else rowCoprimeMask P S a := by
  by_cases h : ∃ i ∈ S, a ∈ P i
  · have hm : rowCoprimeMask P S a = 0 := by simp [rowCoprimeMask, h]
    have hz := row_zero_of_mask_zero P hg S a hm
    simp [localFactor, hm, hz]
  · have hm : rowCoprimeMask P S a = 1 := by simp [rowCoprimeMask, h]
    have h6 : finiteSquarefreeRow P hg S a ^ 6 = 1 := (row_sixth P hg S a).trans hm
    simp only [localFactor, hm, one_mul, ← pow_add]
    rw [pow_eq_pow_mod _ h6, exponent_table]
    split <;> simp

end Rows

def parity (m : ℕ) : Bool := decide (m % 2 = 1)

def evenDouble (m : ℕ) (ε₁ ε₂ : Bool) : Bool := !parity m && ε₁ && ε₂

def b0Exponent (m : ℕ) (ε₁ ε₂ : Bool) : ℕ := m / 2 - bit (evenDouble m ε₁ ε₂)

theorem multiplicity_decomposition (m : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m) :
    2 * b0Exponent m ε₁ ε₂ + 2 * bit (evenDouble m ε₁ ε₂) + bit (parity m) = m := by
  have hmod := Nat.mod_lt m (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div m 2
  cases ε₁ <;> cases ε₂ <;> by_cases h : m % 2 = 1 <;>
    simp [b0Exponent, evenDouble, parity, bit, h] <;> omega

theorem b0Exponent_pos_of_not_retained (m : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m)
    (hret : retained (parity m) ε₁ ε₂ = false) : 0 < b0Exponent m ε₁ ε₂ := by
  have hmod := Nat.mod_lt m (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div m 2
  cases ε₁ <;> cases ε₂ <;> by_cases h : m % 2 = 1 <;>
    simp_all [b0Exponent, evenDouble, parity, retained, bit] <;> omega

section Reassembly
variable {ι κ : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem localFactor_eq_b0 (side ε₁ ε₂ : Bool) (a : O) (m : ℕ) (hm : 0 < m) :
    localFactor P hg S side (parity m) ε₁ ε₂ a =
      (finiteSquarefreeRow P hg S (a ^ bit (retained (parity m) ε₁ ε₂))) ^ 4 *
        rowCoprimeMask P S (a ^ b0Exponent m ε₁ ε₂) := by
  rw [localFactor_eq, row_pow, mask_pow P hg S]
  cases hr : retained (parity m) ε₁ ε₂
  · have hpos := b0Exponent_pos_of_not_retained m ε₁ ε₂ hm hr
    simp only [Bool.false_eq_true, ↓reduceIte, bit, Bool.false_eq_true, pow_zero, one_pow,
      one_mul]
    unfold rowCoprimeMask
    split <;> simp [Nat.ne_of_gt hpos]
  · simp only [↓reduceIte, bit, pow_one]
    exact (row_power_mul_mask_power P hg S a 4 _ (by decide)).symm

def primeProduct (p : κ → O) (B : Finset κ) (v : κ → ℕ) : O := ∏ j ∈ B, p j ^ v j

def cubeRadical (p : κ → O) (B : Finset κ) : O := ∏ j ∈ B, p j

def aLabel (p : κ → O) (B : Finset κ) (ε : κ → Bool) : O :=
  primeProduct p B (fun j => bit (ε j))

def crtLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (side : Bool) : O :=
  primeProduct p B (fun j => crtExponent side (parity (v j)) (ε₁ j) (ε₂ j))

def dilationLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => dilationExponent (parity (v j)) (ε₁ j) (ε₂ j))

def jLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => bit (retained (parity (v j)) (ε₁ j) (ε₂ j)))

def j2Label (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => bit (evenDouble (v j) (ε₁ j) (ε₂ j)))

def squarefreeLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ) : O :=
  primeProduct p B (fun j => bit (parity (v j)))

def b0Label (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => b0Exponent (v j) (ε₁ j) (ε₂ j))

theorem first_pass_label_identity (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (hv : ∀ j ∈ B, 0 < v j) (side : Bool) :
    rowCoprimeMask P S (cubeRadical p B) *
      finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side) *
      finiteSquarefreeRow P hg S (dilationLabel p B v ε₁ ε₂) =
    finiteSquarefreeRow P hg S (jLabel p B v ε₁ ε₂) ^ 4 *
      rowCoprimeMask P S (b0Label p B v ε₁ ε₂) := by
  classical
  simp only [cubeRadical, aLabel, crtLabel, dilationLabel, jLabel, b0Label,
    primeProduct, mask_prod P hg S, row_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [row_pow, row_pow, row_pow]
  convert! localFactor_eq_b0 P hg S side (ε₁ j) (ε₂ j) (p j) (v j) (hv j hj) using 1
  cases side <;> simp only [localFactor, Bool.false_eq_true, ↓reduceIte,
    ← _root_.pow_mul, _root_.Nat.mul_comm]

theorem cube_product_decomposition (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (hv : ∀ j ∈ B, 0 < v j) :
    primeProduct p B v = b0Label p B v ε₁ ε₂ ^ 2 * j2Label p B v ε₁ ε₂ ^ 2 *
      squarefreeLabel p B v := by
  simp only [b0Label, j2Label, squarefreeLabel, primeProduct, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, ← pow_mul, ← pow_add]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  have h := multiplicity_decomposition (v j) (ε₁ j) (ε₂ j) (hv j hj)
  omega

theorem jLabel_eq_squarefree_mul_j2 (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) :
    jLabel p B v ε₁ ε₂ = squarefreeLabel p B v * j2Label p B v ε₁ ε₂ := by
  simp only [jLabel, squarefreeLabel, j2Label, primeProduct, ← Finset.prod_mul_distrib,
    ← pow_add]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  cases hp : parity (v j) <;> cases ε₁ j <;> cases ε₂ j <;>
    simp [bit, retained, evenDouble, hp]

include hg in

theorem radical_mask_absorbs (p : κ → O) (B : Finset κ) (v : κ → ℕ) :
    rowCoprimeMask P S (cubeRadical p B) * rowCoprimeMask P S (primeProduct p B v) =
      rowCoprimeMask P S (cubeRadical p B) := by
  simp only [cubeRadical, primeProduct, mask_prod P hg S, mask_pow P hg S,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  unfold rowCoprimeMask
  split <;> simp

theorem masked_dual_dilation (p : κ → O) (B : Finset κ) (v : κ → ℕ) (z : O) (c : ℂ) :
    rowCoprimeMask P S (cubeRadical p B) * c * star (finiteSquarefreeRow P hg S z) =
      (rowCoprimeMask P S (cubeRadical p B) * c *
        finiteSquarefreeRow P hg S (primeProduct p B v)) *
      star (finiteSquarefreeRow P hg S (z * primeProduct p B v)) := by
  rw [finiteSquarefreeRow_mul, star_mul]
  calc
    _ = (rowCoprimeMask P S (cubeRadical p B) *
        rowCoprimeMask P S (primeProduct p B v)) * c *
        star (finiteSquarefreeRow P hg S z) := by rw [radical_mask_absorbs P hg S]
    _ = _ := by rw [← finiteSquarefreeRow_self_pair P hg S (primeProduct p B v)]; ring

theorem first_pass_after_dual_dilation
    (p : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (z : O) :
    (rowCoprimeMask P S (cubeRadical p B) *
      finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side)) *
      star (finiteSquarefreeRow P hg S z) =
    (finiteSquarefreeRow P hg S (jLabel p B v ε₁ ε₂) ^ 4 *
      rowCoprimeMask P S (b0Label p B v ε₁ ε₂)) *
      star (finiteSquarefreeRow P hg S (z * dilationLabel p B v ε₁ ε₂)) := by
  have hd := masked_dual_dilation P hg S p B
    (fun j => dilationExponent (parity (v j)) (ε₁ j) (ε₂ j)) z
    (finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side))
  change _ = (_ * finiteSquarefreeRow P hg S (dilationLabel p B v ε₁ ε₂)) * _ at hd
  simp only [← mul_assoc] at hd
  rw [first_pass_label_identity P hg S p B v ε₁ ε₂ hv side] at hd
  exact hd

theorem cube_pair_product_decomposition
    (p : κ → O) (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v₁ j + v₂ j) :
    primeProduct p B v₁ * primeProduct p B v₂ =
      b0Label p B (fun j => v₁ j + v₂ j) ε₁ ε₂ ^ 2 *
      j2Label p B (fun j => v₁ j + v₂ j) ε₁ ε₂ ^ 2 *
      squarefreeLabel p B (fun j => v₁ j + v₂ j) := by
  rw [← cube_product_decomposition p B (fun j => v₁ j + v₂ j) ε₁ ε₂ hv]
  simp only [primeProduct, pow_add, Finset.prod_mul_distrib]

end Reassembly

theorem mobius_column_after_dual_dilation
    {ι κ : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (columns : Finset ι) (C : Finset ι → ℂ)
    (p : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (z : O) :
    (∑ S ∈ columns.powerset, FirstCauchyArithmetic.supportMobius P S * C S *
      ((rowCoprimeMask P S (cubeRadical p B) *
        finiteSquarefreeRow P hg S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
        finiteSquarefreeRow P hg S (crtLabel p B v ε₁ ε₂ side)) *
        star (finiteSquarefreeRow P hg S z))) =
    FirstCauchyArithmetic.supportConjugateSum P hg columns
      (fun S => C S * finiteSquarefreeRow P hg S (jLabel p B v ε₁ ε₂) ^ 4 *
        rowCoprimeMask P S (b0Label p B v ε₁ ε₂))
      (z * dilationLabel p B v ε₁ ε₂) := by
  unfold FirstCauchyArithmetic.supportConjugateSum
  apply Finset.sum_congr rfl
  intro S hS
  rw [first_pass_after_dual_dilation P hg S p B v ε₁ ε₂ hv side z]
  ring

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open FiniteGaussPhase MixedCrossSeparation ActualEisensteinCoordinates QuadraticGaussRay
open RayFourExpansion

def quadraticSymbol {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) : ℂ :=
  quadraticRow (fun i => Ideal.span {p i}) hg A (∏ i ∈ B, p i)

theorem quadraticSymbol_eq_cross_product {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) :
    quadraticSymbol p hg A B = ∏ i ∈ A, ∏ k ∈ B, crossSymbol p hg i k ^ 3 := by
  simp only [quadraticSymbol, quadraticRow, finiteSquarefreeRow, map_prod,
    ← Finset.prod_pow, crossSymbol]

theorem quadraticSymbol_mul_reverse {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) :
    quadraticSymbol p hg A B * quadraticSymbol p hg B A = quadraticCrossPhase p hg A B := by
  rw [quadraticSymbol_eq_cross_product, quadraticSymbol_eq_cross_product]
  rw [Finset.prod_comm (s := B) (t := A)]
  simp only [quadraticCrossPhase, Finset.prod_mul_distrib]

theorem quadraticSymbol_eq_zero_of_not_disjoint {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (h : ¬ Disjoint A B) :
    quadraticSymbol p hg A B = 0 := by
  obtain ⟨i, hiA, hiB⟩ := Finset.not_disjoint_iff.mp h
  rw [quadraticSymbol_eq_cross_product]
  apply Finset.prod_eq_zero hiA
  apply Finset.prod_eq_zero hiB
  have hz : Ideal.Quotient.mk (Ideal.span {p i}) (p i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simp only [crossSymbol, hz, MulChar.map_zero, zero_pow (by decide : 3 ≠ 0)]

theorem quadraticSymbol_sq_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (hd : Disjoint A B) :
    quadraticSymbol p hg A B ^ 2 = 1 := by
  rw [quadraticSymbol_eq_cross_product, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro k hk
  have hik : i ≠ k := by
    intro h
    subst k
    exact Finset.disjoint_left.mp hd hi hk
  rw [← pow_mul]
  simpa only [crossSymbol, show 3 * 2 = 6 by decide, map_pow,
    if_neg (prime_generator_not_mem_other p hcop i k hik)] using
      canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)

theorem quadraticSymbol_reciprocity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A B : Finset ι) :
    quadraticSymbol p hg A B =
      quadraticRayPair (residue (∏ i ∈ A, p i)) (residue (∏ i ∈ B, p i)) *
        quadraticSymbol p hg B A := by
  by_cases hd : Disjoint A B
  · have hprod := quadraticSymbol_mul_reverse p hg A B
    rw [quadraticCrossPhase_eq_rayPair p hp hcop hg hc A B hd] at hprod
    have hsq := quadraticSymbol_sq_eq_one p hcop hg B A hd.symm
    calc
      _ = quadraticSymbol p hg A B * (quadraticSymbol p hg B A) ^ 2 := by rw [hsq, mul_one]
      _ = _ := by rw [pow_two, ← mul_assoc, hprod]
  · rw [quadraticSymbol_eq_zero_of_not_disjoint p hg A B hd,
      quadraticSymbol_eq_zero_of_not_disjoint p hg B A (fun h => hd h.symm), mul_zero]

theorem quadraticSymbol_reciprocity_characters {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A B : Finset ι) :
    quadraticSymbol p hg A B =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        crossCoeff χ η * rayCharacter χ (∏ i ∈ A, p i) *
          rayCharacter η (∏ i ∈ B, p i) * quadraticSymbol p hg B A := by
  rw [quadraticSymbol_reciprocity p hp hcop hg hc]
  have hr := quadraticRayPair_character_expansion (∏ i ∈ A, p i) (∏ i ∈ B, p i)
  rw [rayMask_prime_product p hc A, rayMask_prime_product p hc B, one_mul, one_mul] at hr
  rw [hr]
  simp only [Finset.sum_mul]

end QuadraticInitialBound

end

end OAI

end



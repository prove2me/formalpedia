-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0064
-- name    : PNT_ZeroFree_433_0064
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T16:18:48.223537+00:00
-- url     : https://prove2.me/theorems/6fa6af30-1b32-4c8f-81e5-c4c501f0c0dd
-- title:
--   Zero-free region foundations: QuadraticSieve.CoprimeBilinearBound [0064]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.CoprimeBilinearBound
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CoprimeBilinearBound.lean#L76-L619

import Definitions.Def_PNT_ZeroFree_433_0060

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CoprimeBilinearBound.lean#L76-L619
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.CoprimeBilinearBound
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
namespace CoprimeBilinearSieve
open FiniteSieveOperator CoprimeSieveOperator CoprimeMobiusExtension

theorem disjoint_bilinear_expansion {ι n p : Type*} [DecidableEq ι]
    [Fintype n] [Fintype p]
    (B : Finset ι) (left : n → Finset ι) (right : p → Finset ι)
    (hl : ∀ j, left j ⊆ B) (hr : ∀ k, right k ⊆ B)
    (z : n → ℂ) (v : p → ℂ) :
    (∑ j, ∑ k, if Disjoint (left j) (right k) then star (z j) * v k else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        (star (∑ j, if D ⊆ left j then z j else 0) *
          (∑ k, if D ⊆ right k then v k else 0)) := by
  have hp (j : n) (k : p) :
      (if Disjoint (left j) (right k) then star (z j) * v k else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        (if D ⊆ left j ∧ D ⊆ right k then star (z j) * v k else 0) := by
    calc
      _ = (if Disjoint (left j) (right k) then (1 : ℂ) else 0) *
          (star (z j) * v k) := by split_ifs <;> simp
      _ = _ := by
        rw [disjoint_indicator_expansion B _ _ (hl j) (hr k), Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro D _
        split_ifs <;> simp
  simp_rw [hp]
  calc
    _ = ∑ j, ∑ D ∈ B.powerset, ∑ k, (-1 : ℂ) ^ D.card *
        (if D ⊆ left j ∧ D ⊆ right k then star (z j) * v k else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ D ∈ B.powerset, ∑ j, ∑ k, (-1 : ℂ) ^ D.card *
        (if D ⊆ left j ∧ D ⊆ right k then star (z j) * v k else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D _
      simp_rw [← Finset.mul_sum]
      congr 1
      simp only [star_sum, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      by_cases hj : D ⊆ left j <;> by_cases hk : D ⊆ right k <;> simp [hj, hk]

theorem coprime_bilinear_operator_bound {ι m n p : Type*} [DecidableEq ι]
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (B : Finset ι) (left : n → Finset ι) (right : p → Finset ι)
    (hl : ∀ j, left j ⊆ B) (hr : ∀ k, right k ⊆ B)
    (A : Matrix m n ℂ) (C : Matrix m p ℂ) (a : n → ℂ) (b : p → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if Disjoint (left j) (right k) then
      star (A i j * a j) * (C i k * b k) else 0‖) ^ 2 ≤
      (‖operator A‖ ^ 2 * ∑ j, (2 : ℝ) ^ (left j).card * ‖a j‖ ^ 2) *
      (‖operator C‖ ^ 2 * ∑ k, (2 : ℝ) ^ (right k).card * ‖b k‖ ^ 2) := by
  let X (D : Finset ι) (i : m) : ℂ := ∑ j, A i j * (if D ⊆ left j then a j else 0)
  let Y (D : Finset ι) (i : m) : ℂ := ∑ k, C i k * (if D ⊆ right k then b k else 0)
  have heq (i : m) :
      (∑ j, ∑ k, if Disjoint (left j) (right k) then
        star (A i j * a j) * (C i k * b k) else 0) =
        ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card * (star (X D i) * Y D i) := by
    simpa only [X, Y, mul_ite, mul_zero] using
      disjoint_bilinear_expansion B left right hl hr (fun j => A i j * a j)
        (fun k => C i k * b k)
  have hnorm :
      (∑ i, ‖∑ j, ∑ k, if Disjoint (left j) (right k) then
        star (A i j * a j) * (C i k * b k) else 0‖) ≤
        ∑ D ∈ B.powerset, ∑ i, ‖X D i‖ * ‖Y D i‖ := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i _
    rw [heq]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro D _
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_star]
    exact le_rfl
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (B.powerset ×ˢ (Finset.univ : Finset m))
    (fun di => ‖X di.1 di.2‖) (fun di => ‖Y di.1 di.2‖)
  simp only [Finset.sum_product] at hCS
  have hX : (∑ D ∈ B.powerset, ∑ i, ‖X D i‖ ^ 2) ≤
      ‖operator A‖ ^ 2 * ∑ j, (2 : ℝ) ^ (left j).card * ‖a j‖ ^ 2 := by
    calc
      _ ≤ ∑ D ∈ B.powerset, ‖operator A‖ ^ 2 *
          ∑ j, ‖if D ⊆ left j then a j else 0‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro D _
        exact energy_bound A _
      _ = _ := by rw [← Finset.mul_sum, masked_coefficient_energy B left hl a]
  have hY : (∑ D ∈ B.powerset, ∑ i, ‖Y D i‖ ^ 2) ≤
      ‖operator C‖ ^ 2 * ∑ k, (2 : ℝ) ^ (right k).card * ‖b k‖ ^ 2 := by
    calc
      _ ≤ ∑ D ∈ B.powerset, ‖operator C‖ ^ 2 *
          ∑ k, ‖if D ⊆ right k then b k else 0‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro D _
        exact energy_bound C _
      _ = _ := by rw [← Finset.mul_sum, masked_coefficient_energy B right hr b]
  exact (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hnorm 2).trans
    (hCS.trans (mul_le_mul hX hY (by positivity) (by positivity)))

end CoprimeBilinearSieve

namespace IdealCoprimeBilinearSieve
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum IdealCoprimeSieveOperator FiniteSieveOperator

theorem support_weighted_energy_bound {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ j, (2 : ℝ) ^ (primeSupport (column j)).card * ‖a j‖ ^ 2) ≤
      (supportConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact (support_card_bound ε hε (column j) (hcol j)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm j) hε.le)
      (supportConstant_pos ε hε).le)

theorem ideal_coprime_bilinear_operator_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε)
    (left : n → Ideal O) (right : p → Ideal O)
    (hl0 : ∀ j, left j ≠ 0) (hr0 : ∀ k, right k ≠ 0)
    (N₁ N₂ : ℝ) (hN₁ : 0 ≤ N₁) (_hN₂ : 0 ≤ N₂)
    (hlN : ∀ j, (Ideal.absNorm (left j) : ℝ) ≤ N₁)
    (hrN : ∀ k, (Ideal.absNorm (right k) : ℝ) ≤ N₂)
    (A : Matrix m n ℂ) (C : Matrix m p ℂ) (a : n → ℂ) (b : p → ℂ) :
    (∑ i, ‖∑ j, ∑ k, if IsCoprime (left j) (right k) then
      star (A i j * a j) * (C i k * b k) else 0‖) ^ 2 ≤
      (‖operator A‖ ^ 2 * (supportConstant ε hε * N₁ ^ ε) * ∑ j, ‖a j‖ ^ 2) *
      (‖operator C‖ ^ 2 * (supportConstant ε hε * N₂ ^ ε) * ∑ k, ‖b k‖ ^ 2) := by
  let B : Finset (Ideal O) :=
    (Finset.univ.biUnion (fun j => primeSupport (left j))) ∪
      (Finset.univ.biUnion (fun k => primeSupport (right k)))
  have hl (j : n) : primeSupport (left j) ⊆ B := by
    intro P hP
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hP⟩))
  have hr (k : p) : primeSupport (right k) ⊆ B := by
    intro P hP
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hP⟩))
  have h := CoprimeBilinearSieve.coprime_bilinear_operator_bound B
    (fun j => primeSupport (left j)) (fun k => primeSupport (right k)) hl hr A C a b
  simp_rw [primeSupport_disjoint_iff (hl0 _) (hr0 _)] at h
  apply h.trans
  apply mul_le_mul
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (support_weighted_energy_bound ε hε left hl0 N₁ hlN a) (sq_nonneg ‖operator A‖)
  · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (support_weighted_energy_bound ε hε right hr0 N₂ hrN b) (sq_nonneg ‖operator C‖)
  · positivity
  · have hpos := (supportConstant_pos ε hε).le
    positivity

end IdealCoprimeBilinearSieve

namespace DivisorBlockCauchy
abbrev O := ActualEisensteinCubic.O
open IdealMobiusDivisorSum FiniteSieveOperator IdealCoprimeSieveOperator

theorem divisor_mask_energy {n : Type*} [Fintype n]
    (S : Finset (Ideal O)) (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (a : n → ℂ) :
    (∑ D ∈ S, ∑ j, ‖if D ∣ column j then a j else 0‖ ^ 2) ≤
      ∑ j, ((idealDivisors (column j)).card : ℝ) * ‖a j‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  have hsub : S.filter (fun D => D ∣ column j) ⊆ idealDivisors (column j) := by
    intro D hD
    exact (mem_idealDivisors (hcol j)).mpr (Finset.mem_filter.mp hD).2
  have hite (D : Ideal O) : ‖if D ∣ column j then a j else 0‖ ^ 2 =
      if D ∣ column j then ‖a j‖ ^ 2 else 0 := by split_ifs <;> simp
  simp_rw [hite]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (sq_nonneg _)

def divisorConstant (ε : ℝ) (hε : 0 < ε) : ℝ :=
  (IdealDivisorBound.ideal_divisor_small_power ε hε).choose

theorem divisorConstant_pos (ε : ℝ) (hε : 0 < ε) : 0 < divisorConstant ε hε :=
  (IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.1

theorem divisor_mask_energy_small_power {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (S : Finset (Ideal O))
    (column : n → Ideal O) (hcol : ∀ j, column j ≠ 0)
    (N : ℝ) (hnorm : ∀ j, (Ideal.absNorm (column j) : ℝ) ≤ N) (a : n → ℂ) :
    (∑ D ∈ S, ∑ j, ‖if D ∣ column j then a j else 0‖ ^ 2) ≤
      (divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2 := by
  apply (divisor_mask_energy S column hcol a).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2
    (column j) (hcol j)).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm j) hε.le) (divisorConstant_pos ε hε).le

theorem rectangular_cauchy {α β : Type*} (S : Finset α) (T : Finset β)
    (H : α → β → ℝ) (E : α → ℝ) (F : β → ℝ) (C : ℝ)
    (_hC : 0 ≤ C) (hH : ∀ d ∈ S, ∀ e ∈ T, (H d e) ^ 2 ≤ C * E d * F e) :
    (∑ d ∈ S, ∑ e ∈ T, H d e) ^ 2 ≤
      (S.card : ℝ) * T.card * C * (∑ d ∈ S, E d) * (∑ e ∈ T, F e) := by
  classical
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (S ×ˢ T)
    (fun _ => (1 : ℝ)) (fun x => H x.1 x.2)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_product, Nat.cast_mul, Finset.sum_product] at hCS
  have hsum : (∑ d ∈ S, ∑ e ∈ T, (H d e) ^ 2) ≤
      C * (∑ d ∈ S, E d) * (∑ e ∈ T, F e) := by
    calc
      _ ≤ ∑ d ∈ S, ∑ e ∈ T, C * E d * F e := by
        apply Finset.sum_le_sum
        intro d hd
        exact Finset.sum_le_sum (fun e he => hH d hd e he)
      _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]
  apply hCS.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum
    (show (0 : ℝ) ≤ (S.card : ℝ) * T.card by positivity)

end DivisorBlockCauchy

namespace IdealDivisorBilinearBlocks
abbrev O := ActualEisensteinCubic.O
open FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy

def blockValue {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (left : n → Ideal O) (right : p → Ideal O)
    (A : Ideal O → Matrix m n ℂ) (B : Ideal O → Matrix m p ℂ)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : ℝ :=
  ∑ i, ‖∑ j, ∑ k, if IsCoprime (left j) (right k) then
    star (A D i j * (if D ∣ left j then a j else 0)) *
      (B E i k * (if E ∣ right k then b k else 0)) else 0‖

theorem blockValue_nonneg {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (left : n → Ideal O) (right : p → Ideal O)
    (A : Ideal O → Matrix m n ℂ) (B : Ideal O → Matrix m p ℂ)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) :
    0 ≤ blockValue left right A B a b D E :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem divisor_block_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (left : n → Ideal O) (right : p → Ideal O)
    (hl0 : ∀ j, left j ≠ 0) (hr0 : ∀ k, right k ≠ 0)
    (N₁ N₂ : ℝ) (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hlN : ∀ j, (Ideal.absNorm (left j) : ℝ) ≤ N₁)
    (hrN : ∀ k, (Ideal.absNorm (right k) : ℝ) ≤ N₂)
    (A : Ideal O → Matrix m n ℂ) (B : Ideal O → Matrix m p ℂ)
    (a : n → ℂ) (b : p → ℂ) (UA UB : ℝ) (hUA : 0 ≤ UA) (hUB : 0 ≤ UB)
    (hA : ∀ D ∈ S, ‖operator (A D)‖ ^ 2 ≤ UA)
    (hB : ∀ E ∈ T, ‖operator (B E)‖ ^ 2 ≤ UB) :
    (∑ D ∈ S, ∑ E ∈ T, blockValue left right A B a b D E) ^ 2 ≤
      (S.card : ℝ) * T.card *
        (UA * UB * (supportConstant ε hε * N₁ ^ ε) *
          (supportConstant ε hε * N₂ ^ ε)) *
        ((divisorConstant ε hε * N₁ ^ ε) * ∑ j, ‖a j‖ ^ 2) *
        ((divisorConstant ε hε * N₂ ^ ε) * ∑ k, ‖b k‖ ^ 2) := by
  let EL (D : Ideal O) : ℝ := ∑ j, ‖if D ∣ left j then a j else 0‖ ^ 2
  let ER (E : Ideal O) : ℝ := ∑ k, ‖if E ∣ right k then b k else 0‖ ^ 2
  let C : ℝ := UA * UB * (supportConstant ε hε * N₁ ^ ε) *
    (supportConstant ε hε * N₂ ^ ε)
  have hs := (supportConstant_pos ε hε).le
  have hd := (divisorConstant_pos ε hε).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hEL (D) : 0 ≤ EL D := by dsimp [EL]; positivity
  have hER (E) : 0 ≤ ER E := by dsimp [ER]; positivity
  have hp (D : Ideal O) (hD : D ∈ S) (E : Ideal O) (hE : E ∈ T) :
      (blockValue left right A B a b D E) ^ 2 ≤ C * EL D * ER E := by
    have hh := IdealCoprimeBilinearSieve.ideal_coprime_bilinear_operator_bound
      ε hε left right hl0 hr0 N₁ N₂ hN₁ hN₂ hlN hrN (A D) (B E)
      (fun j => if D ∣ left j then a j else 0)
      (fun k => if E ∣ right k then b k else 0)
    change (blockValue left right A B a b D E) ^ 2 ≤
      (‖operator (A D)‖ ^ 2 * (supportConstant ε hε * N₁ ^ ε) * EL D) *
      (‖operator (B E)‖ ^ 2 * (supportConstant ε hε * N₂ ^ ε) * ER E) at hh
    apply hh.trans
    calc
      _ ≤ (UA * (supportConstant ε hε * N₁ ^ ε) * EL D) *
          (UB * (supportConstant ε hε * N₂ ^ ε) * ER E) := by
        gcongr
        · exact hA D hD
        · exact hB E hE
      _ = _ := by dsimp [C]; ring
  have hc := rectangular_cauchy S T (blockValue left right A B a b) EL ER C hC hp
  have he1 := divisor_mask_energy_small_power ε hε S left hl0 N₁ hlN a
  have he2 := divisor_mask_energy_small_power ε hε T right hr0 N₂ hrN b
  apply hc.trans
  change (S.card : ℝ) * T.card * C * (∑ D ∈ S, EL D) * (∑ E ∈ T, ER E) ≤ _
  change (∑ D ∈ S, EL D) ≤ _ at he1
  change (∑ E ∈ T, ER E) ≤ _ at he2
  dsimp only [C]
  gcongr

end IdealDivisorBilinearBlocks

namespace FiniteSieveRestriction
open FiniteSieveOperator

variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

def extendByZero (S : Finset n) (f : n → p) (u : n → ℂ) (k : p) : ℂ :=
  ∑ j ∈ S, if f j = k then u j else 0

omit [Fintype n] [Fintype p] [DecidableEq n] in
theorem extendByZero_apply_image (S : Finset n) (f : n → p) (u : n → ℂ)
    (hf : Set.InjOn f S) (j : n) (hj : j ∈ S) : extendByZero S f u (f j) = u j := by
  unfold extendByZero
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    simp only [if_neg (fun h => hkj (hf hk hj h))]
  · exact fun h => (h hj).elim

omit [Fintype n] [Fintype p] [DecidableEq n] in
theorem extendByZero_zero (S : Finset n) (f : n → p) (u : n → ℂ)
    (k : p) (hk : k ∉ S.image f) : extendByZero S f u k = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  exact if_neg (fun h => hk (Finset.mem_image.mpr ⟨j, hj, h⟩))

omit [Fintype n] [DecidableEq n] in
theorem extendByZero_energy (S : Finset n) (f : n → p) (u : n → ℂ)
    (hf : Set.InjOn f S) :
    (∑ k, ‖extendByZero S f u k‖ ^ 2) = ∑ j ∈ S, ‖u j‖ ^ 2 := by
  calc
    _ = ∑ k ∈ S.image f, ‖extendByZero S f u k‖ ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro k _ hk
      simp [extendByZero_zero S f u k hk]
    _ = ∑ j ∈ S, ‖extendByZero S f u (f j)‖ ^ 2 := by
      rw [Finset.sum_image]
      exact fun j hj k hk h => hf hj hk h
    _ = _ := Finset.sum_congr rfl (fun j hj => by rw [extendByZero_apply_image S f u hf j hj])

omit [Fintype n] [DecidableEq n] in
theorem extendByZero_matrix {m : Type*} (S : Finset n) (f : n → p)
    (u : n → ℂ) (A : Matrix m p ℂ) (i : m) :
    (∑ k, A i k * extendByZero S f u k) = ∑ j ∈ S, A i (f j) * u j := by
  simp only [extendByZero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (f j)]
  · simp
  · intro k _ hkj
    simp [Ne.symm hkj]
  · simp

theorem masked_column_restriction_norm_le {m : Type*} [Fintype m] [DecidableEq m]
    (S : Finset n) (f : n → p) (hf : Set.InjOn f S) (A : Matrix m p ℂ) :
    ‖operator (fun i j => if j ∈ S then A i (f j) else 0)‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  let v : EuclideanSpace ℂ p := WithLp.toLp 2 (extendByZero S f u)
  have hv : ‖v‖ ≤ ‖u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change (∑ k, ‖extendByZero S f u k‖ ^ 2) ≤ ∑ j, ‖u j‖ ^ 2
    rw [extendByZero_energy S f u hf]
    exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖u j‖)
  have heq : operator (fun i j => if j ∈ S then A i (f j) else 0) u = operator A v := by
    ext i
    change (∑ j, (if j ∈ S then A i (f j) else 0) * u j) =
      ∑ k, A i k * extendByZero S f u k
    rw [extendByZero_matrix]
    simp only [ite_mul, zero_mul, ← Finset.sum_filter]
    simp
  rw [heq]
  exact ((operator A).le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))

theorem column_restriction_norm_le {m : Type*} [Fintype m] [DecidableEq m]
    (f : n → p) (hf : Function.Injective f) (A : Matrix m p ℂ) :
    ‖operator (fun i j => A i (f j))‖ ≤ ‖operator A‖ := by
  simpa only [Finset.mem_univ, ite_true] using
    masked_column_restriction_norm_le Finset.univ f hf.injOn A

theorem row_restriction_norm_le {m : Type*} [Fintype m] [DecidableEq m]
    (f : n → p) (hf : Function.Injective f) (A : Matrix p m ℂ) :
    ‖operator (fun i j => A (f i) j)‖ ≤ ‖operator A‖ := by
  let B : Matrix n m ℂ := fun i j => A (f i) j
  have h := column_restriction_norm_le f hf A.conjTranspose
  change ‖operator B.conjTranspose‖ ≤ ‖operator A.conjTranspose‖ at h
  rw [operator_conjTranspose_norm B, operator_conjTranspose_norm A] at h
  exact h

theorem submatrix_norm_le {m q : Type*} [Fintype m] [Fintype q]
    [DecidableEq m] [DecidableEq q]
    (r : m → q) (hr : Function.Injective r) (c : n → p) (hc : Function.Injective c)
    (A : Matrix q p ℂ) :
    ‖operator (fun i j => A (r i) (c j))‖ ≤ ‖operator A‖ :=
  (row_restriction_norm_le r hr (fun i j => A i (c j))).trans
    (column_restriction_norm_le c hc A)

end FiniteSieveRestriction

open scoped BigOperators
namespace FiniteSieveOperator

theorem squared_norm_le_of_energy {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ a : n → ℂ, (∑ i, ‖∑ j, A i j * a j‖ ^ 2) ≤ C * ∑ j, ‖a j‖ ^ 2) :
    ‖operator A‖ ^ 2 ≤ C := by
  have hop : ‖operator A‖ ≤ Real.sqrt C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg C)
    intro a
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg a))).mp
    simpa only [mul_pow, Real.sq_sqrt hC, EuclideanSpace.norm_sq_eq, operator_apply] using h a
  simpa only [Real.sq_sqrt hC] using pow_le_pow_left₀ (norm_nonneg _) hop 2

end FiniteSieveOperator

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
abbrev O := ActualEisensteinCubic.O
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss

theorem idealSexticRow_ambient
    (F G : Finset (Ideal O)) (hFp : ∀ I ∈ F, I ≠ ⊥) (hGp : ∀ I ∈ G, I ≠ ⊥)
    (hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hGg : ∀ I ∈ G, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (I : Ideal O) (hIF : I ∈ F) (hIG : I ∈ G) (z : O) :
    idealSexticRow F hFp hFg I z = idealSexticRow G hGp hGg I z := by
  let idx (i : primePool F) (hi : i ∈ idealSupport F I) : primePool G :=
    ⟨i.val, mem_primePool_iff.mpr ⟨I, hIG, (mem_idealSupport_iff F I i).mp hi⟩⟩
  unfold idealSexticRow finiteSquarefreeRow
  apply Finset.prod_bij idx
  · intro i hi
    exact (mem_idealSupport_iff G I (idx i hi)).mpr ((mem_idealSupport_iff F I i).mp hi)
  · intro i hi j hj hij
    exact Subtype.ext (congrArg (fun k : primePool G => k.val) hij)
  · intro j hj
    let i : primePool F := ⟨j.val, mem_primePool_iff.mpr
      ⟨I, hIF, (mem_idealSupport_iff G I j).mp hj⟩⟩
    have hi : i ∈ idealSupport F I :=
      (mem_idealSupport_iff F I i).mpr ((mem_idealSupport_iff G I j).mp hj)
    exact ⟨i, hi, Subtype.ext rfl⟩
  · intro i hi
    rfl

def Admissible (I : Ideal O) : Prop :=
  I ≠ 0 ∧ Squarefree I ∧ ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
    lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2

theorem singletonPositive (I : Ideal O) (h : Admissible I) : ∀ J ∈ ({I} : Finset (Ideal O)), J ≠ ⊥ := by
  intro J hJ
  rcases Finset.mem_singleton.mp hJ with rfl
  exact h.1

theorem singletonGood (I : Ideal O) (h : Admissible I) :
    ∀ J ∈ ({I} : Finset (Ideal O)), ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors J,
      goodLambda ∉ P := by
  intro J hJ P hP
  rcases Finset.mem_singleton.mp hJ with rfl
  exact (h.2.2 P hP).1

def quadraticRow (I : Ideal O) (z : O) : ℂ :=
  if h : Admissible I then
    (idealSexticRow {I} (singletonPositive I h) (singletonGood I h) I z) ^ 3
  else 0

theorem quadraticRow_eq (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I : Ideal O) (hI : I ∈ F) (z : O) :
    quadraticRow I z =
      (idealSexticRow F (fun J hJ => (hF J hJ).1)
        (fun J hJ P hP => (hF J hJ).2.2 P hP |>.1) I z) ^ 3 := by
  rw [quadraticRow, dif_pos (hF I hI)]
  congr 1
  exact idealSexticRow_ambient {I} F (singletonPositive I (hF I hI))
    (fun J hJ => (hF J hJ).1) (singletonGood I (hF I hI))
    (fun J hJ P hP => (hF J hJ).2.2 P hP |>.1) I (Finset.mem_singleton_self I) hI z

def idealRange (X : ℝ) : Finset (Ideal O) := (idealsUpTo ⌊X⌋₊).filter Admissible

theorem mem_idealRange {X : ℝ} {I : Ideal O} :
    I ∈ idealRange X ↔ Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
  rw [idealRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, ha⟩
    refine ⟨ha, ?_⟩
    have hX : 0 ≤ X := by
      by_contra hn
      have hz : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hX)
  · rintro ⟨ha, hN⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => ha.1 (Ideal.absNorm_eq_zero_iff.mp h)),
      Nat.le_floor hN⟩, ha⟩

theorem idealRange_mono {X Y : ℝ} (h : X ≤ Y) : idealRange X ⊆ idealRange Y := by
  intro I hI
  rcases mem_idealRange.mp hI with ⟨ha, hN⟩
  exact mem_idealRange.mpr ⟨ha, hN.trans h⟩

def matrix (M N : ℝ) : Matrix (idealRange M) (idealRange N) ℂ :=
  fun I J => quadraticRow J.val (primaryGenerator I.val)

def sieveNorm (M N : ℝ) : ℝ := ‖FiniteSieveOperator.operator (matrix M N)‖ ^ 2

theorem sieveNorm_nonneg (M N : ℝ) : 0 ≤ sieveNorm M N := sq_nonneg _

def rangeInclusion {X Y : ℝ} (h : X ≤ Y) (I : idealRange X) : idealRange Y :=
  ⟨I.val, idealRange_mono h I.property⟩

theorem rangeInclusion_injective {X Y : ℝ} (h : X ≤ Y) :
    Function.Injective (rangeInclusion h) := by
  intro I J heq
  exact Subtype.ext (congrArg (fun x : idealRange Y => x.val) heq)

theorem sieveNorm_mono {M N M' N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    sieveNorm M N ≤ sieveNorm M' N' := by
  have h := FiniteSieveRestriction.submatrix_norm_le
    (rangeInclusion hM) (rangeInclusion_injective hM)
    (rangeInclusion hN) (rangeInclusion_injective hN) (matrix M' N')
  change ‖FiniteSieveOperator.operator (matrix M N)‖ ≤
    ‖FiniteSieveOperator.operator (matrix M' N')‖ at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (fun i j => quadraticRow (cols j) (primaryGenerator (rows i)))‖ ^ 2 ≤
      sieveNorm M N := by
  let r : m → idealRange M := fun i => ⟨rows i, mem_idealRange.mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (matrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem energy_bound (M N : ℝ) (a : idealRange N → ℂ) :
    (∑ I : idealRange M, ‖∑ J : idealRange N,
      quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2) ≤
      sieveNorm M N * ∑ J, ‖a J‖ ^ 2 :=
  FiniteSieveOperator.energy_bound (matrix M N) a

end CanonicalQuadraticSieve

end

end OAI

end



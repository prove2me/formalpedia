-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0055
-- name    : PNT_ZeroFree_433_0055
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T15:38:51.927657+00:00
-- url     : https://prove2.me/theorems/f87507fc-c9cd-41b0-aa1f-62193f4eb96a
-- title:
--   Zero-free region foundations: QuadraticSieve.FiniteOperator, RSCompat [0055]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.FiniteOperator
--   - RSCompat
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/FiniteOperator.lean#L77-L797
--   Locally proved Lean 4.33.1 compatibility lemmas: RSCompat.lean#L8-L41

import Definitions.Def_PNT_ZeroFree_433_0054
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Squarefree.Basic

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/FiniteOperator.lean#L77-L797
Locally proved Lean 4.33.1 compatibility lemmas: RSCompat.lean#L8-L41
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.FiniteOperator
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

open scoped BigOperators
namespace FiniteSieveOperator

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def operator (A : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  A.toEuclideanLin.toContinuousLinearMap

omit [DecidableEq m] in
@[simp] theorem operator_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) (i : m) :
    operator A x i = ∑ j, A i j * x j := rfl

theorem operator_conjTranspose (A : Matrix m n ℂ) :
    operator A.conjTranspose = (operator A).adjoint := by
  unfold operator
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]

theorem operator_conjTranspose_norm (A : Matrix m n ℂ) :
    ‖operator A.conjTranspose‖ = ‖operator A‖ := by
  rw [operator_conjTranspose]
  exact ContinuousLinearMap.adjoint.norm_map _

omit [DecidableEq m] in
theorem operator_zero : operator (0 : Matrix m n ℂ) = 0 := by
  ext x i
  simp

omit [DecidableEq m] in
theorem operator_add (A B : Matrix m n ℂ) : operator (A + B) = operator A + operator B := by
  ext x i
  simp [add_mul, Finset.sum_add_distrib]

omit [DecidableEq m] in
theorem operator_smul (c : ℂ) (A : Matrix m n ℂ) : operator (c • A) = c • operator A := by
  ext x i
  simp [Finset.mul_sum, mul_assoc]

omit [DecidableEq m] in
theorem operator_sum {κ : Type*} (S : Finset κ) (A : κ → Matrix m n ℂ) :
    operator (∑ k ∈ S, A k) = ∑ k ∈ S, operator (A k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [operator_zero]
  | @insert a S ha ih => simp only [Finset.sum_insert ha, operator_add, ih]

omit [DecidableEq m] in
theorem diagonal_twist_norm_le (A : Matrix m n ℂ) (l : m → ℂ) (r : n → ℂ)
    (hl : ∀ i, ‖l i‖ ≤ 1) (hr : ∀ j, ‖r j‖ ≤ 1) :
    ‖operator (fun i j => l i * A i j * r j)‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  let y : EuclideanSpace ℂ n := WithLp.toLp 2 (fun j => r j * x j)
  have hy : ‖y‖ ≤ ‖x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro j _
    change ‖r j * x j‖ ^ 2 ≤ ‖x j‖ ^ 2
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hr j)
  have heq (i : m) : operator (fun i j => l i * A i j * r j) x i = l i * operator A y i := by
    simp only [operator_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change l i * A i j * r j * x j = l i * (A i j * (r j * x j))
    ring
  have hz : ‖operator (fun i j => l i * A i j * r j) x‖ ≤ ‖operator A y‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    rw [heq, norm_mul]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_of_le_one_left (norm_nonneg _) (hl i)
  exact hz.trans ((operator A).le_opNorm y |>.trans
    (mul_le_mul_of_nonneg_left hy (norm_nonneg _)))

omit [DecidableEq m] in
theorem separated_phase_norm_le {κ : Type*} [Fintype κ]
    (A B : Matrix m n ℂ) (c : κ → ℂ) (l : κ → m → ℂ) (r : κ → n → ℂ)
    (hl : ∀ k i, ‖l k i‖ ≤ 1) (hr : ∀ k j, ‖r k j‖ ≤ 1)
    (heq : ∀ i j, A i j = ∑ k, c k * (l k i * B i j * r k j)) :
    ‖operator A‖ ≤ (∑ k, ‖c k‖) * ‖operator B‖ := by
  let T : κ → Matrix m n ℂ := fun k i j => l k i * B i j * r k j
  have hA : A = ∑ k, c k • T k := by
    ext i j
    rw [Matrix.sum_apply]
    exact heq i j
  have hOp : operator A = ∑ k, c k • operator (T k) := by
    calc
      _ = operator (∑ k, c k • T k) := congrArg operator hA
      _ = ∑ k, operator (c k • T k) := operator_sum _ _
      _ = _ := Finset.sum_congr rfl (fun k _ => operator_smul (c k) (T k))
  rw [hOp]
  calc
    _ ≤ ∑ k, ‖c k • operator (T k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖c k‖ * ‖operator B‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (diagonal_twist_norm_le B (l k) (r k) (hl k) (hr k))
        (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

omit [DecidableEq m] in
theorem energy_bound (A : Matrix m n ℂ) (u : n → ℂ) :
    (∑ i, ‖∑ j, A i j * u j‖ ^ 2) ≤ ‖operator A‖ ^ 2 * ∑ j, ‖u j‖ ^ 2 := by
  let x : EuclideanSpace ℂ n := WithLp.toLp 2 u
  have h := (operator A).le_opNorm x
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [mul_pow, EuclideanSpace.norm_sq_eq, operator_apply, x, PiLp.toLp_apply] using hs

end FiniteSieveOperator

section
open scoped BigOperators Classical
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT RayFourExpansion

def quadraticMatrix {ι m n : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (rows : m → Finset ι) (cols : n → Finset ι) : Matrix m n ℂ :=
  fun i j => quadraticSymbol p hg (cols j) (rows i)

def quadraticSieveNorm {ι m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (rows : m → Finset ι) (cols : n → Finset ι) : ℝ :=
  ‖FiniteSieveOperator.operator (quadraticMatrix p hg rows cols)‖ ^ 2

theorem quadraticSieveNorm_energy {ι m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (rows : m → Finset ι) (cols : n → Finset ι) (a : n → ℂ) :
    (∑ i, ‖∑ j, quadraticSymbol p hg (cols j) (rows i) * a j‖ ^ 2) ≤
      quadraticSieveNorm p hg rows cols * ∑ j, ‖a j‖ ^ 2 :=
  FiniteSieveOperator.energy_bound (quadraticMatrix p hg rows cols) a

theorem quadratic_matrix_norm_reverse_le
    {ι m n : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (rows : m → Finset ι) (cols : n → Finset ι) :
    ‖FiniteSieveOperator.operator (quadraticMatrix p hg rows cols)‖ ≤
      512 * ‖FiniteSieveOperator.operator (quadraticMatrix p hg cols rows)‖ := by
  let A := quadraticMatrix p hg rows cols
  let B := (quadraticMatrix p hg cols rows).conjTranspose
  let c : RayCharacter × RayCharacter → ℂ := fun k => crossCoeff k.1 k.2
  let l : RayCharacter × RayCharacter → m → ℂ := fun k i =>
    rayCharacter k.2 (∏ s ∈ rows i, p s)
  let r : RayCharacter × RayCharacter → n → ℂ := fun k j =>
    rayCharacter k.1 (∏ s ∈ cols j, p s)
  have hB (i : m) (j : n) : B i j = quadraticSymbol p hg (rows i) (cols j) := by
    change star (quadraticSymbol p hg (rows i) (cols j)) = _
    exact quadraticRow_star _ _ _ _
  have hl (k : RayCharacter × RayCharacter) (i : m) : ‖l k i‖ ≤ 1 :=
    FiniteRayExpansion.norm_char_le_one k.2 _
  have hr (k : RayCharacter × RayCharacter) (j : n) : ‖r k j‖ ≤ 1 :=
    FiniteRayExpansion.norm_char_le_one k.1 _
  have hA (i : m) (j : n) : A i j = ∑ k, c k * (l k i * B i j * r k j) := by
    rw [hB, Fintype.sum_prod_type]
    change quadraticSymbol p hg (cols j) (rows i) = _
    rw [quadraticSymbol_reciprocity_characters p hp hcop hg hc]
    apply Finset.sum_congr rfl
    intro χ _
    apply Finset.sum_congr rfl
    intro η _
    dsimp [c, l, r]
    ring
  have hmass : (∑ k, ‖c k‖) ≤ 512 := by
    simpa only [c, Fintype.sum_prod_type] using crossCoeff_sum_norm_le
  calc
    _ ≤ (∑ k, ‖c k‖) * ‖FiniteSieveOperator.operator B‖ :=
      FiniteSieveOperator.separated_phase_norm_le A B c l r hl hr hA
    _ ≤ 512 * ‖FiniteSieveOperator.operator B‖ :=
      mul_le_mul_of_nonneg_right hmass (norm_nonneg _)
    _ = _ := by
      change 512 * ‖FiniteSieveOperator.operator
        (quadraticMatrix p hg cols rows).conjTranspose‖ = _
      rw [FiniteSieveOperator.operator_conjTranspose_norm]

theorem quadraticSieveNorm_reverse_le
    {ι m n : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (rows : m → Finset ι) (cols : n → Finset ι) :
    quadraticSieveNorm p hg rows cols ≤ 262144 * quadraticSieveNorm p hg cols rows := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (quadratic_matrix_norm_reverse_le p hp hcop hg hc rows cols) 2
  simpa only [quadraticSieveNorm, mul_pow, show (512 : ℝ) ^ 2 = 262144 by norm_num] using h

end QuadraticInitialBound

open scoped BigOperators Classical
open Filter IdealMobiusDivisorSum UniqueFactorizationMonoid

namespace IdealDivisorBound
abbrev O := ActualEisensteinCubic.O

theorem divisor_ne_zero {I J : Ideal O} (hI : I ≠ ⊥) (hJ : J ∈ idealDivisors I) : J ≠ 0 := by
  intro hz
  have hd := (mem_idealDivisors hI).mp hJ
  rw [hz, zero_dvd_iff] at hd
  exact hI hd

theorem divisor_card_le_product (I : Ideal O) (hI : I ≠ ⊥) :
    (idealDivisors I).card ≤
      ∏ P ∈ primeSupport I, ((normalizedFactors I).count P + 1) := by
  change (idealDivisors I).card ≤
    ∏ P ∈ (normalizedFactors I).toFinset, ((normalizedFactors I).count P + 1)
  rw [← Multiset.card_Iic]
  apply Finset.card_le_card_of_injOn normalizedFactors
  · intro J hJ
    change normalizedFactors J ∈ Finset.Iic (normalizedFactors I)
    rw [Finset.mem_Iic]
    exact (dvd_iff_normalizedFactors_le_normalizedFactors
      (divisor_ne_zero hI hJ) hI).mp ((mem_idealDivisors hI).mp hJ)
  · intro J hJ K hK he
    calc
      J = (normalizedFactors J).prod := (Ideal.prod_normalizedFactors_eq_self (divisor_ne_zero hI hJ)).symm
      _ = (normalizedFactors K).prod := congrArg Multiset.prod he
      _ = K := Ideal.prod_normalizedFactors_eq_self (divisor_ne_zero hI hK)

theorem linear_le_geometric (b : ℝ) (hb : 1 < b) (n : ℕ) :
    (n : ℝ) + 1 ≤ (1 + (b - 1)⁻¹) * b ^ n := by
  have hδ : 0 < b - 1 := sub_pos.mpr hb
  have hn := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ b by linarith) n
  have hn' : (n : ℝ) ≤ b ^ n / (b - 1) := by
    apply (le_div_iff₀ hδ).mpr
    linarith
  have h1 : (1 : ℝ) ≤ b ^ n := one_le_pow₀ hb.le
  calc
    (n : ℝ) + 1 ≤ b ^ n / (b - 1) + b ^ n := add_le_add hn' h1
    _ = _ := by ring

theorem support_norm_two_le {I P : Ideal O} (hP : P ∈ primeSupport I) :
    2 ≤ Ideal.absNorm P := by
  have hp := support_prime hP
  have h0 : Ideal.absNorm P ≠ 0 := by
    intro h
    exact hp.ne_zero (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm P ≠ 1 := by
    intro h
    have ht := Ideal.absNorm_eq_one_iff.mp h
    apply hp.not_isUnit
    rw [ht]
    simpa only [Ideal.one_eq_top] using (show IsUnit (1 : Ideal O) from isUnit_one)
  omega

theorem norm_factor_product (I : Ideal O) (hI : I ≠ ⊥) :
    (∏ P ∈ primeSupport I, (Ideal.absNorm P : ℝ) ^ (normalizedFactors I).count P) =
      Ideal.absNorm I := by
  have he := congrArg (fun J : Ideal O => (Ideal.absNorm J : ℝ))
    (Ideal.prod_normalizedFactors_eq_self hI)
  rw [Finset.prod_multiset_count] at he
  simpa only [primeSupport, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow] using he

theorem ideal_divisor_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal O, I ≠ ⊥ →
      ((idealDivisors I).card : ℝ) ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  let small : Finset (Ideal O) :=
    (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset
  let b : ℝ := (2 : ℝ) ^ ε
  have hb : 1 < b := by
    dsimp [b]
    exact Real.one_lt_rpow (by norm_num) hε
  let c : ℝ := 1 + (b - 1)⁻¹
  have hc : 1 ≤ c := by
    dsimp [c]
    have hi : 0 ≤ (b - 1)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hb.le)
    linarith
  refine ⟨c ^ small.card, by positivity, ?_⟩
  intro I hI
  let S := primeSupport I
  let e := fun P : Ideal O => (normalizedFactors I).count P
  have hfac (P : Ideal O) (hP : P ∈ S) :
      ((e P + 1 : ℕ) : ℝ) ≤
        (if P ∈ small then c else 1) * ((Ideal.absNorm P : ℝ) ^ ε) ^ e P := by
    have hnorm : (2 : ℝ) ≤ Ideal.absNorm P := by exact_mod_cast support_norm_two_le hP
    have hbase : b ≤ (Ideal.absNorm P : ℝ) ^ ε :=
      Real.rpow_le_rpow (by norm_num) hnorm hε.le
    by_cases hp : P ∈ small
    · rw [if_pos hp]
      have hlin := linear_le_geometric b hb (e P)
      have hl : ((e P + 1 : ℕ) : ℝ) ≤ c * b ^ e P := by
        simpa only [Nat.cast_add, Nat.cast_one, c] using hlin
      apply hl.trans
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hbase _) (by positivity)
    · rw [if_neg hp, one_mul]
      have hn : N ≤ Ideal.absNorm P := by
        have : ¬ Ideal.absNorm P ≤ N := fun h => hp (by simpa [small] using h)
        omega
      have hp2 := hN _ hn
      calc
        _ ≤ (2 : ℝ) ^ e P := by
          have hh := one_add_mul_sub_le_pow (by norm_num : (-1 : ℝ) ≤ 2) (e P)
          norm_num at hh ⊢
          linarith
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) hp2 _
  have hprod := Finset.prod_le_prod
    (fun P (_ : P ∈ S) => (by positivity : (0 : ℝ) ≤ ((e P + 1 : ℕ) : ℝ))) hfac
  have hconst : (∏ P ∈ S, if P ∈ small then c else 1) ≤ c ^ small.card := by
    have he : (∏ P ∈ S, if P ∈ small then c else 1) = c ^ (S ∩ small).card := by
      simp []
    rw [he]
    exact pow_le_pow_right₀ hc (Finset.card_le_card Finset.inter_subset_right)
  have hpow : (∏ P ∈ S, ((Ideal.absNorm P : ℝ) ^ ε) ^ e P) =
      (Ideal.absNorm I : ℝ) ^ ε := by
    calc
      _ = ∏ P ∈ S, ((Ideal.absNorm P : ℝ) ^ e P) ^ ε := by
        apply Finset.prod_congr rfl
        intro P hP
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
          ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        rw [mul_comm]
      _ = (∏ P ∈ S, (Ideal.absNorm P : ℝ) ^ e P) ^ ε :=
        Real.finsetProd_rpow S _ (fun _ _ => by positivity) ε
      _ = _ := by rw [norm_factor_product I hI]
  have hcard : ((idealDivisors I).card : ℝ) ≤ ∏ P ∈ S, ((e P + 1 : ℕ) : ℝ) := by
    exact_mod_cast divisor_card_le_product I hI
  apply hcard.trans
  rw [Finset.prod_mul_distrib, hpow] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hconst (by positivity))

end IdealDivisorBound
end

namespace SecondPassFiber
open scoped BigOperators Classical
open IdealMobiusDivisorSum ConcretePrimeRowBridge

abbrev O := ActualEisensteinCubic.O

@[ext] structure OldTuple where
  core : Fin 8 → Ideal O
  v : Ideal O
  j2 : Ideal O
  b2 : Ideal O
  row : O

structure Valid (x : OldTuple) (F b0 : Ideal O) (y : O) : Prop where
  label : x.core 0 * x.core 1 * x.core 2 * x.v = F
  j_split : x.core 3 * x.j2 = x.core 0
  b_split : x.core 4 * x.b2 = b0 ^ 2 * x.j2 ^ 2 * x.core 3
  a1 : x.core 5 ∣ x.core 4 * x.b2
  a2 : x.core 6 ∣ x.core 4 * x.b2
  d : x.core 7 ∣ F * b0
  row_eq : idealGenerator (x.core 7) * idealGenerator (x.core 2) * x.row = y

def divisorTarget (F b0 : Ideal O) : Ideal O := (F * b0) ^ 2

theorem core_dvd_target (x : OldTuple) (F b0 : Ideal O) (y : O)
    (h : Valid x F b0 y) (i : Fin 8) : x.core i ∣ divisorTarget F b0 := by
  have hJ : x.core 0 ∣ F := by
    rw [← h.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  have hC : x.core 1 ∣ F := by
    rw [← h.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  have he : x.core 2 ∣ F := by
    rw [← h.label]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hs : x.core 3 ∣ F := by
    apply dvd_trans _ hJ
    rw [← h.j_split]
    exact dvd_mul_right _ _
  have hFT : F ∣ divisorTarget F b0 := by
    dsimp [divisorTarget]
    exact (dvd_mul_right F b0).trans (dvd_pow_self _ (by decide))
  have hbprod : x.core 4 * x.b2 ∣ divisorTarget F b0 := by
    apply dvd_trans (b := b0 ^ 2 * x.core 0 ^ 2)
    · refine ⟨x.core 3, ?_⟩
      rw [h.b_split, ← h.j_split]
      ring
    · dsimp [divisorTarget]
      rw [mul_pow, mul_comm (F ^ 2)]
      exact mul_dvd_mul_left _ (pow_dvd_pow_of_dvd hJ 2)
  fin_cases i
  · exact hJ.trans hFT
  · exact hC.trans hFT
  · exact he.trans hFT
  · exact hs.trans hFT
  · exact (dvd_mul_right _ _).trans hbprod
  · exact h.a1.trans hbprod
  · exact h.a2.trans hbprod
  · exact h.d.trans (dvd_pow_self _ (by decide))

theorem target_ne_zero (F b0 : Ideal O) (hF : F ≠ ⊥) (hb0 : b0 ≠ ⊥) :
    divisorTarget F b0 ≠ 0 := pow_ne_zero _ (mul_ne_zero hF hb0)

theorem core_ne_zero (x : OldTuple) (F b0 : Ideal O) (y : O)
    (hF : F ≠ ⊥) (hb0 : b0 ≠ ⊥) (h : Valid x F b0 y) (i : Fin 8) :
    x.core i ≠ 0 := by
  intro he
  have hd := core_dvd_target x F b0 y h i
  rw [he, zero_dvd_iff] at hd
  exact target_ne_zero F b0 hF hb0 hd

theorem valid_core_injective (F b0 : Ideal O) (y : O)
    (hF : F ≠ ⊥) (hb0 : b0 ≠ ⊥) {x z : OldTuple}
    (hx : Valid x F b0 y) (hz : Valid z F b0 y) (hcore : x.core = z.core) : x = z := by
  have hc (i : Fin 8) : x.core i = z.core i := congrFun hcore i
  have hv : x.v = z.v := by
    apply mul_left_cancel₀
      (mul_ne_zero (mul_ne_zero (core_ne_zero x F b0 y hF hb0 hx 0)
        (core_ne_zero x F b0 y hF hb0 hx 1)) (core_ne_zero x F b0 y hF hb0 hx 2))
    calc
      _ = F := hx.label
      _ = _ := by simpa only [hc] using hz.label.symm
  have hj : x.j2 = z.j2 := by
    apply mul_left_cancel₀ (core_ne_zero x F b0 y hF hb0 hx 3)
    calc
      _ = x.core 0 := hx.j_split
      _ = _ := by simpa only [hc] using hz.j_split.symm
  have hb : x.b2 = z.b2 := by
    apply mul_left_cancel₀ (core_ne_zero x F b0 y hF hb0 hx 4)
    calc
      _ = b0 ^ 2 * x.j2 ^ 2 * x.core 3 := hx.b_split
      _ = _ := by simpa only [hc, hj] using hz.b_split.symm
  have hgen (i : Fin 8) : idealGenerator (x.core i) ≠ 0 := by
    intro he
    apply core_ne_zero x F b0 y hF hb0 hx i
    rw [← span_idealGenerator (x.core i), he]
    simp
  have hr : x.row = z.row := by
    apply mul_left_cancel₀ (mul_ne_zero (hgen 7) (hgen 2))
    calc
      _ = y := hx.row_eq
      _ = _ := by simpa only [hc] using hz.row_eq.symm
  exact OldTuple.ext hcore hv hj hb hr

theorem valid_tuple_card_le (s : Finset OldTuple) (F b0 : Ideal O) (y : O)
    (hF : F ≠ ⊥) (hb0 : b0 ≠ ⊥) (hs : ∀ x ∈ s, Valid x F b0 y) :
    s.card ≤ (idealDivisors (divisorTarget F b0)).card ^ 8 := by
  let D := idealDivisors (divisorTarget F b0)
  let encode (x : s) : Fin 8 → D := fun i => ⟨x.val.core i, by
    apply (mem_idealDivisors (target_ne_zero F b0 hF hb0)).mpr
    exact core_dvd_target x.val F b0 y (hs x.val x.property) i⟩
  have hinj : Function.Injective encode := by
    intro x z he
    apply Subtype.ext
    apply valid_core_injective F b0 y hF hb0 (hs x.val x.property) (hs z.val z.property)
    funext i
    exact congrArg Subtype.val (congrFun he i)
  have hc := Fintype.card_le_of_injective encode hinj
  simpa [D] using hc

theorem valid_tuple_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (F b0 : Ideal O) (y : O),
      F ≠ ⊥ → b0 ≠ ⊥ → (∀ x ∈ s, Valid x F b0 y) →
      (s.card : ℝ) ≤ C * ((Ideal.absNorm F : ℝ) * Ideal.absNorm b0) ^ ε := by
  obtain ⟨C, hC, h⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 16) (by positivity)
  refine ⟨C ^ 8, by positivity, ?_⟩
  intro s F b0 y hF hb0 hs
  have hc : (s.card : ℝ) ≤ ((idealDivisors (divisorTarget F b0)).card : ℝ) ^ 8 := by
    exact_mod_cast valid_tuple_card_le s F b0 y hF hb0 hs
  have hd := pow_le_pow_left₀ (by positivity)
    (h (divisorTarget F b0) (target_ne_zero F b0 hF hb0)) 8
  apply hc.trans (hd.trans_eq ?_)
  rw [mul_pow]
  congr 1
  simp only [divisorTarget, map_pow, map_mul, Nat.cast_pow, Nat.cast_mul]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

def newLabel (x : OldTuple) : Ideal O := x.core 0 * x.core 1 * x.core 2 * x.v
def newRow (x : OldTuple) : O :=
  idealGenerator (x.core 7) * idealGenerator (x.core 2) * x.row

theorem second_energy_pushforward (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (P : Ideal O × O → ℂ) (B H : ℝ),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ H →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ H) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (newLabel x, newRow x)‖ ^ 2) ≤
        B * C * (H * Ideal.absNorm b0) ^ ε * ∑ z ∈ t, ‖P z‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := valid_tuple_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w P B H hb0 hB hH hvalid hmap ht hnorm hw
  have hpush := DescentWeightedCauchy.bounded_energy_pushforward
    s t (fun x => (newLabel x, newRow x)) w P B hmap hw
  apply hpush.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hval : ∀ x ∈ s.filter (fun x => (newLabel x, newRow x) = z), Valid x z.1 b0 z.2 := by
    intro x hx
    have he := (Finset.mem_filter.mp hx).2
    have hv := hvalid x (Finset.mem_filter.mp hx).1
    have h1 : newLabel x = z.1 := congrArg Prod.fst he
    have h2 : newRow x = z.2 := congrArg Prod.snd he
    simpa only [h1, h2] using hv
  have hfiber := hc (s.filter (fun x => (newLabel x, newRow x) = z)) z.1 b0 z.2
    (ht z hz) hb0 hval
  have hgrowth : (Ideal.absNorm z.1 : ℝ) * Ideal.absNorm b0 ≤ H * Ideal.absNorm b0 :=
    mul_le_mul_of_nonneg_right (hnorm z hz) (by positivity)
  have hcard := hfiber.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hgrowth hε.le) hC.le)
  have hterm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard hB) (sq_nonneg ‖P z‖)
  simpa only [mul_assoc] using hterm

end SecondPassFiber

open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic

theorem conductorExponent_val (parityBit ε₁ ε₂ : Bool) :
    (conductorExponent parityBit ε₁ ε₂).val = (bit ε₁ + 5 * bit ε₂ + 3 * bit parityBit) % 6 := by
  cases parityBit <;> cases ε₁ <;> cases ε₂ <;> decide

theorem cube_pair_exponent_mod (m₁ m₂ : ℕ) (ε₁ ε₂ : Bool) :
    (bit ε₁ + 5 * bit ε₂ + 3 * m₁ + 15 * m₂) % 6 =
      (conductorExponent (parity (m₁ + m₂)) ε₁ ε₂).val := by
  have hmod := Nat.mod_lt (m₁ + m₂) (by decide : 0 < 2)
  rw [conductorExponent_val]
  cases ε₁ <;> cases ε₂ <;> by_cases h : (m₁ + m₂) % 2 = 1 <;>
    norm_num [parity, bit, h] <;> omega

def cubePairLocal (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (m₁ m₂ : ℕ) (ε₁ ε₂ : Bool) (z : O) : ℂ :=
  let q := canonicalSextic P hg (Ideal.Quotient.mk P z)
  q ^ bit ε₁ * star (q ^ bit ε₂) * q ^ (3 * m₁) * star (q ^ (3 * m₂))

theorem cubePairLocal_eq_character
    (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (m₁ m₂ : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m₁ + m₂ + bit ε₁ + bit ε₂) (z : O) :
    cubePairLocal P hg m₁ m₂ ε₁ ε₂ z =
      (canonicalSextic P hg ^ (conductorExponent (parity (m₁ + m₂)) ε₁ ε₂).val)
        (Ideal.Quotient.mk P z) := by
  let q := canonicalSextic P hg (Ideal.Quotient.mk P z)
  have hstar : star q = q ^ 5 := by
    have hs := canonicalSextic_conj_as_row_label P hg z
    change star q = q * q ^ 4 at hs
    rw [hs]
    ring
  have hleft : cubePairLocal P hg m₁ m₂ ε₁ ε₂ z =
      q ^ (bit ε₁ + 5 * bit ε₂ + 3 * m₁ + 15 * m₂) := by
    change q ^ bit ε₁ * star (q ^ bit ε₂) * q ^ (3 * m₁) * star (q ^ (3 * m₂)) = _
    simp only [star_pow, hstar, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hleft]
  by_cases hz : z ∈ P
  · have hq : q = 0 := by
      change canonicalSextic P hg (Ideal.Quotient.mk P z) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
    rw [hq, Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
    exact zero_pow (by omega)
  · have hu : IsUnit (Ideal.Quotient.mk P z) := by
      let : Field (O ⧸ P) := Ideal.Quotient.field P
      exact isUnit_iff_ne_zero.mpr (fun h => hz (Ideal.Quotient.eq_zero_iff_mem.mp h))
    have h6 : q ^ 6 = 1 := by
      have h := canonicalSextic_sixth_power_mask P hg z
      simp only [map_pow, if_neg hz] at h
      exact h
    rw [pow_eq_pow_mod _ h6, cube_pair_exponent_mod]
    exact (MulChar.pow_apply_coe _ _ hu.unit).symm

def cubeConductorSupport {κ : Type*} (B : Finset κ) (v₁ v₂ : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : Finset κ :=
  B.filter (fun j => conductorExponent (parity (v₁ j + v₂ j)) (ε₁ j) (ε₂ j) ≠ 0)

def cubePrincipalSupport {κ : Type*} (B : Finset κ) (v₁ v₂ : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : Finset κ :=
  B.filter (fun j => conductorExponent (parity (v₁ j + v₂ j)) (ε₁ j) (ε₂ j) = 0)

theorem cubeConductorExponent_ne_zero {κ : Type*} (B : Finset κ)
    (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool) (j : cubeConductorSupport B v₁ v₂ ε₁ ε₂) :
    (conductorExponent (parity (v₁ j.val + v₂ j.val)) (ε₁ j.val) (ε₂ j.val)).val ≠ 0 := by
  exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp j.property).2

theorem cubeConductorExponent_lt_six {κ : Type*} (B : Finset κ)
    (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool) (j : cubeConductorSupport B v₁ v₂ ε₁ ε₂) :
    (conductorExponent (parity (v₁ j.val + v₂ j.val)) (ε₁ j.val) (ε₂ j.val)).val < 6 :=
  ZMod.val_lt _

def multiplicityRow {κ : Type*} (P : κ → Ideal O) [∀ j, (P j).IsMaximal]
    (hg : ∀ j, lambda ∉ P j) (B : Finset κ) (v : κ → ℕ) (z : O) : ℂ :=
  ∏ j ∈ B, canonicalSextic (P j) (hg j) (Ideal.Quotient.mk (P j) z) ^ v j

def cubePairRow {κ : Type*} (P : κ → Ideal O) [∀ j, (P j).IsMaximal]
    (hg : ∀ j, lambda ∉ P j) (B : Finset κ) (v₁ v₂ : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (z : O) : ℂ :=
  finiteSquarefreeRow P hg (B.filter fun j => ε₁ j) z *
    star (finiteSquarefreeRow P hg (B.filter fun j => ε₂ j) z) *
    multiplicityRow P hg B v₁ z ^ 3 * star (multiplicityRow P hg B v₂ z ^ 3)

private theorem row_filter_eq_power_product {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hg : ∀ j, lambda ∉ P j)
    (B : Finset κ) (ε : κ → Bool) (z : O) :
    finiteSquarefreeRow P hg (B.filter fun j => ε j) z =
      ∏ j ∈ B, canonicalSextic (P j) (hg j) (Ideal.Quotient.mk (P j) z) ^ bit (ε j) := by
  simp only [finiteSquarefreeRow, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j hj
  cases ε j <;> simp [bit]

theorem cubePairRow_eq_product {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hg : ∀ j, lambda ∉ P j)
    (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool) (z : O) :
    cubePairRow P hg B v₁ v₂ ε₁ ε₂ z =
      ∏ j ∈ B, cubePairLocal (P j) (hg j) (v₁ j) (v₂ j) (ε₁ j) (ε₂ j) z := by
  simp only [cubePairRow, row_filter_eq_power_product, multiplicityRow,
    ← Finset.prod_pow, star_prod, ← Finset.prod_mul_distrib, ← pow_mul]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [cubePairLocal, Nat.mul_comm]

private theorem principal_product_eq_mask {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (B : Finset κ) (z : O) :
    (∏ j ∈ B, (1 : MulChar (O ⧸ P j) ℂ) (Ideal.Quotient.mk (P j) z)) =
      rowCoprimeMask P B z := by
  by_cases h : ∃ j ∈ B, z ∈ P j
  · rw [rowCoprimeMask, if_pos h]
    obtain ⟨j, hj, hz⟩ := h
    apply Finset.prod_eq_zero hj
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
  · rw [rowCoprimeMask, if_neg h]
    apply Finset.prod_eq_one
    intro j hj
    apply MulChar.one_apply
    let : Field (O ⧸ P j) := Ideal.Quotient.field (P j)
    apply isUnit_iff_ne_zero.mpr
    exact fun hz => h ⟨j, hj, Ideal.Quotient.eq_zero_iff_mem.mp hz⟩

theorem cubePairRow_conductor_selection {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hg : ∀ j, lambda ∉ P j)
    (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hcover : ∀ j ∈ B, 0 < v₁ j + v₂ j + bit (ε₁ j) + bit (ε₂ j)) (z : O) :
    cubePairRow P hg B v₁ v₂ ε₁ ε₂ z =
      rowCoprimeMask P (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z *
        finiteSexticRow (fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ => P j.val)
          (fun j => hg j.val)
          (fun j => (conductorExponent (parity (v₁ j.val + v₂ j.val))
            (ε₁ j.val) (ε₂ j.val)).val) z := by
  let e := fun j => conductorExponent (parity (v₁ j + v₂ j)) (ε₁ j) (ε₂ j)
  let f := fun j => (canonicalSextic (P j) (hg j) ^ (e j).val) (Ideal.Quotient.mk (P j) z)
  have hlocal : cubePairRow P hg B v₁ v₂ ε₁ ε₂ z = ∏ j ∈ B, f j := by
    rw [cubePairRow_eq_product]
    apply Finset.prod_congr rfl
    intro j hj
    exact cubePairLocal_eq_character (P j) (hg j) (v₁ j) (v₂ j)
      (ε₁ j) (ε₂ j) (hcover j hj) z
  have hzero : (∏ j ∈ B.filter (fun j => e j = 0), f j) =
      rowCoprimeMask P (cubePrincipalSupport B v₁ v₂ ε₁ ε₂) z := by
    rw [← principal_product_eq_mask]
    apply Finset.prod_congr rfl
    intro j hj
    have he : e j = 0 := (Finset.mem_filter.mp hj).2
    simp only [f, he, ZMod.val_zero, pow_zero]
  rw [hlocal, ← Finset.prod_filter_mul_prod_filter_not B (fun j => e j = 0) f, hzero]
  congr 1
  exact (Finset.prod_coe_sort (s := cubeConductorSupport B v₁ v₂ ε₁ ε₂) (f := f)).symm

theorem cubeConductorPrimes_pairwise_coprime {κ : Type*}
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hinj : Function.Injective P)
    (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool) :
    Pairwise (Function.onFun IsCoprime
      (fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ => P j.val)) := by
  intro i j hij
  apply Ideal.isCoprime_of_isMaximal
  exact fun he => hij (Subtype.ext (hinj he))

open scoped SchwartzMap ContDiff
open ConcreteTraceCRT
open EisensteinSchwartzPoisson (paperRadialFourier)

def cubePairPoissonKernel {κ : Type*} [DecidableEq κ]
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ j, lambda ∉ P j) (B : Finset κ) (v₁ v₂ : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) : ℂ :=
  let Q := fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ => P j.val
  let hQ := cubeConductorPrimes_pairwise_coprime P hinj B v₁ v₂ ε₁ ε₂
  let eg := fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ =>
    (conductorExponent (parity (v₁ j.val + v₂ j.val)) (ε₁ j.val) (ε₂ j.val)).val
  let row := finiteSexticRow Q (fun j => hg j.val) eg
  let c := finitePrimeModulus Q
  ((scale : ℂ) * canonicalNormalizedGauss Q hQ (fun j => hg j.val) eg /
    (‖eisEmbedding c‖ : ℂ)) *
    ∑ E ∈ (cubePrincipalSupport B v₁ v₂ ε₁ ε₂).powerset,
      let d := primeSubsetGenerator P E
      ((UniqueFactorizationMonoid.moebius (∏ j ∈ E, P j) : ℂ) * row d /
        (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, star (row h) * paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding c‖ ^ 2))

theorem cubePairRow_radial_poisson {κ : Type*} [DecidableEq κ]
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ j, lambda ∉ P j) (hc : ∀ j, ringChar (O ⧸ P j) ≠ 2)
    (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hcover : ∀ j ∈ B, 0 < v₁ j + v₂ j + bit (ε₁ j) + bit (ε₂ j))
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, cubePairRow P hg B v₁ v₂ ε₁ ε₂ z *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      cubePairPoissonKernel P hinj hg B v₁ v₂ ε₁ ε₂ W scale := by
  simp_rw [cubePairRow_conductor_selection P hg B v₁ v₂ ε₁ ε₂ hcover]
  exact canonical_masked_radial_poisson_collected P hinj
    (cubePrincipalSupport B v₁ v₂ ε₁ ε₂)
    (fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ => P j.val)
    (cubeConductorPrimes_pairwise_coprime P hinj B v₁ v₂ ε₁ ε₂)
    (fun j => hg j.val) (fun j => hc j.val)
    (fun j => (conductorExponent (parity (v₁ j.val + v₂ j.val)) (ε₁ j.val) (ε₂ j.val)).val)
    (cubeConductorExponent_ne_zero B v₁ v₂ ε₁ ε₂)
    (cubeConductorExponent_lt_six B v₁ v₂ ε₁ ε₂) W scale hscale

end FirstPassCubeLabels

end

end OAI

end

-- Source module: RSCompat
section
open scoped BigOperators

namespace Finset

theorem sum_le_sum_of_injOn {ι α N : Type*} [AddCommMonoid N] [Preorder N]
    [AddLeftMono N] [DecidableEq α]
    {s : Finset ι} {t : Finset α} {f : ι → N} {g : α → N}
    (e : ι → α) (he : Set.InjOn e s) (ht : image e s ⊆ t)
    (h : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ a ∈ t, a ∉ image e s → 0 ≤ g a) :
    ∑ i ∈ s, f i ≤ ∑ a ∈ t, g a := by
  calc
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := sum_le_sum h
    _ = ∑ a ∈ image e s, g a := (sum_image he).symm
    _ ≤ ∑ a ∈ t, g a := sum_le_sum_of_subset_of_nonneg ht hg

end Finset

theorem exists_sq_mul_squarefree {R : Type*} [CommMonoidWithZero R]
    [IsCancelMulZero R] [UniqueFactorizationMonoid R] (x : R) :
    ∃ a b : R, a ^ 2 * b = x ∧ Squarefree b := by
  refine UniqueFactorizationMonoid.induction_on_prime x ?_ ?_ ?_
  · exact ⟨0, 1, by simp, squarefree_one⟩
  · intro y hy
    exact ⟨1, y, by simp, hy.squarefree⟩
  · intro y p _hy hp ih
    obtain ⟨a, d, had, hd⟩ := ih
    by_cases hpd : p ∣ d
    · obtain ⟨e, rfl⟩ := hpd
      refine ⟨a * p, e, ?_, hd.of_mul_right⟩
      calc
        (a * p) ^ 2 * e = p * (a ^ 2 * (p * e)) := by simp only [mul_pow, pow_two]; ac_rfl
        _ = p * y := by rw [had]
    · refine ⟨a, p * d, ?_, ?_⟩
      · calc
          a ^ 2 * (p * d) = p * (a ^ 2 * d) := by ac_rfl
          _ = p * y := by rw [had]
      · exact squarefree_mul_iff.mpr ⟨hp.irreducible.isRelPrime_iff_not_dvd.mpr hpd, hp.squarefree, hd⟩

end



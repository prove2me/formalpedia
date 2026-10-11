-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0072
-- name    : PNT_ZeroFree_433_0072
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T16:40:39.365465+00:00
-- url     : https://prove2.me/theorems/b4414bce-037e-4e79-ba2e-8818939d3d52
-- title:
--   Zero-free region foundations: QuadraticSieve.DivisorBlocks [0072]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.DivisorBlocks
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/DivisorBlocks.lean#L78-L708

import Definitions.Def_PNT_ZeroFree_433_0065

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/DivisorBlocks.lean#L78-L708
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.DivisorBlocks
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
namespace CanonicalQuadraticSieve

section
open IdealCoprimeSieveOperator DivisorBlockCauchy IdealDivisorBilinearBlocks

def quotientBlock {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : ℝ :=
  blockValue left right (fun D => quotientMatrix D rows left)
    (fun E => quotientMatrix E rows right) a b D E

theorem canonical_divisor_block_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, quotientBlock rows left right a b D E) ^ 2 ≤
      256 ^ 2 * D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
        (supportConstant ε hε * divisorConstant ε hε) ^ 2 * (N ^ ε) ^ 4 *
        (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2) := by
  have hS0 (D) (hD : D ∈ S) : D ≠ 0 := by
    intro hz
    have hh := (hS D hD).1
    simp only [hz, map_zero, Nat.cast_zero] at hh
    linarith
  have hT0 (E) (hE : E ∈ T) : E ≠ 0 := by
    intro hz
    have hh := (hT E hE).1
    simp only [hz, map_zero, Nat.cast_zero] at hh
    linarith
  have hA (D) (hD : D ∈ S) :
      ‖FiniteSieveOperator.operator (quotientMatrix D rows left)‖ ^ 2 ≤ sieveNorm M (N / D₁) := by
    apply (quotientMatrix_squared_norm_le D (hS0 D hD) rows left hr hl M N hrows hleft).trans
    exact sieveNorm_mono le_rfl (div_le_div_of_nonneg_left (by linarith) (by linarith) (hS D hD).1)
  have hB (E) (hE : E ∈ T) :
      ‖FiniteSieveOperator.operator (quotientMatrix E rows right)‖ ^ 2 ≤ sieveNorm M (N / D₂) := by
    apply (quotientMatrix_squared_norm_le E (hT0 E hE) rows right hr hri M N hrows hright).trans
    exact sieveNorm_mono le_rfl (div_le_div_of_nonneg_left (by linarith) (by linarith) (hT E hE).1)
  have hsCard := DescentFiberCost.finite_ideal_count_real S (2 * D₁) (by linarith)
    hS0 (fun D hD => (hS D hD).2)
  have htCard := DescentFiberCost.finite_ideal_count_real T (2 * D₂) (by linarith)
    hT0 (fun E hE => (hT E hE).2)
  have hh := divisor_block_bound ε hε S T left right (fun j => (hleft j).1.1)
    (fun k => (hright k).1.1) N N (by linarith) (by linarith)
    (fun j => (hleft j).2) (fun k => (hright k).2)
    (fun D => quotientMatrix D rows left) (fun E => quotientMatrix E rows right) a b
    (sieveNorm M (N / D₁)) (sieveNorm M (N / D₂)) (sieveNorm_nonneg _ _) (sieveNorm_nonneg _ _) hA hB
  have hs := (supportConstant_pos ε hε).le
  have hd := (divisorConstant_pos ε hε).le
  have hb1 := sieveNorm_nonneg M (N / D₁)
  have hb2 := sieveNorm_nonneg M (N / D₂)
  change (∑ D ∈ S, ∑ E ∈ T, quotientBlock rows left right a b D E) ^ 2 ≤ _ at hh
  apply hh.trans
  calc
    _ ≤ (128 * (2 * D₁)) * (128 * (2 * D₂)) *
        (sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
          (supportConstant ε hε * N ^ ε) * (supportConstant ε hε * N ^ ε)) *
        ((divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) *
        ((divisorConstant ε hε * N ^ ε) * ∑ k, ‖b k‖ ^ 2) := by gcongr
    _ = _ := by ring

end

section
open ConcretePrimeRowBridge ActualEisensteinCubic

theorem quadraticRow_norm_le_one (I : Ideal O) (z : O) : ‖quadraticRow I z‖ ≤ 1 := by
  by_cases hI : Admissible I
  · rw [quadraticRow, dif_pos hI]
    exact QuadraticMainOperatorBound.ideal_quadraticRow_norm_le_one {I}
      (singletonPositive I hI) (singletonGood I hI) I z
  · simp [quadraticRow, hI]

theorem quadraticRow_mul (I J : Ideal O) (hIJ : Admissible (I * J)) (z : O) :
    quadraticRow (I * J) z = quadraticRow I z * quadraticRow J z := by
  have hI : Admissible I := admissible_of_dvd hIJ (dvd_mul_right I J)
  have hJ : Admissible J := admissible_of_dvd hIJ (dvd_mul_left J I)
  let F : Finset (Ideal O) := {I, J, I * J}
  have hF : ∀ K ∈ F, Admissible K := by
    intro K hK
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hK
    rcases hK with rfl | rfl | rfl
    · exact hI
    · exact hJ
    · exact hIJ
  have hIF : I ∈ F := by simp [F]
  have hJF : J ∈ F := by simp [F]
  have hIJF : I * J ∈ F := by simp [F]
  have hu : idealSupport F (I * J) = idealSupport F I ∪ idealSupport F J := by
    ext P
    simp only [mem_idealSupport_iff, UniqueFactorizationMonoid.normalizedFactors_mul hI.1 hJ.1,
      Multiset.mem_add, Finset.mem_union]
  have hd : Disjoint (idealSupport F I) (idealSupport F J) := by
    apply Finset.disjoint_left.mpr
    intro P hPI hPJ
    have hpI := (mem_idealSupport_iff F I P).mp hPI
    have hpJ := (mem_idealSupport_iff F J P).mp hPJ
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P.val hpI
    have hi : P.val ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpI
    have hj : P.val ∣ J := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpJ
    exact hp.not_isUnit ((IsRelPrime.of_squarefree_mul hIJ.2.1) hi hj)
  rw [quadraticRow_eq F hF (I * J) hIJF z, quadraticRow_eq F hF I hIF z,
    quadraticRow_eq F hF J hJF z]
  unfold idealSexticRow finiteSquarefreeRow
  rw [hu, Finset.prod_union hd, mul_pow]

theorem quadraticRow_divisor_factor (I D : Ideal O) (hI : Admissible I) (hD : D ∣ I) (z : O) :
    quadraticRow I z = quadraticRow D z * quadraticRow (idealQuotient D I) z := by
  have h := quadraticRow_mul D (idealQuotient D I) (by rwa [idealQuotient_mul hD]) z
  simpa only [idealQuotient_mul hD] using h

end

open IdealDivisorBilinearBlocks CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy

def originalBlock {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : ℝ :=
  blockValue left right (fun _ i j => quadraticRow (left j) (primaryGenerator (rows i)))
    (fun _ i k => quadraticRow (right k) (primaryGenerator (rows i))) a b D E

theorem original_entry_factor {m n : Type*} (rows : m → Ideal O) (cols : n → Ideal O)
    (hcols : ∀ j, Admissible (cols j)) (a : n → ℂ) (D : Ideal O) (i : m) (j : n) :
    quadraticRow (cols j) (primaryGenerator (rows i)) * (if D ∣ cols j then a j else 0) =
      quadraticRow D (primaryGenerator (rows i)) *
        (quotientMatrix D rows cols i j * (if D ∣ cols j then a j else 0)) := by
  by_cases h : D ∣ cols j
  · simp only [h, ite_true, quotientMatrix]
    rw [quadraticRow_divisor_factor (cols j) D (hcols j) h]
    ring
  · simp [h, quotientMatrix]

theorem originalBlock_le_quotientBlock {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) :
    originalBlock rows left right a b D E ≤ quotientBlock rows left right a b D E := by
  change (∑ i, _) ≤ ∑ i, _
  apply Finset.sum_le_sum
  intro i _
  have heq : (∑ j, ∑ k, if IsCoprime (left j) (right k) then
      star (quadraticRow (left j) (primaryGenerator (rows i)) * (if D ∣ left j then a j else 0)) *
      (quadraticRow (right k) (primaryGenerator (rows i)) * (if E ∣ right k then b k else 0)) else 0) =
      (star (quadraticRow D (primaryGenerator (rows i))) * quadraticRow E (primaryGenerator (rows i))) *
        (∑ j, ∑ k, if IsCoprime (left j) (right k) then
          star (quotientMatrix D rows left i j * (if D ∣ left j then a j else 0)) *
          (quotientMatrix E rows right i k * (if E ∣ right k then b k else 0)) else 0) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : IsCoprime (left j) (right k)
    · rw [if_pos h, if_pos h]
      rw [original_entry_factor rows left hleft a D i j,
        original_entry_factor rows right hright b E i k, star_mul]
      ring
    · simp only [if_neg h, mul_zero]
  change ‖∑ j, ∑ k, if IsCoprime (left j) (right k) then
      star (quadraticRow (left j) (primaryGenerator (rows i)) * (if D ∣ left j then a j else 0)) *
      (quadraticRow (right k) (primaryGenerator (rows i)) * (if E ∣ right k then b k else 0)) else 0‖ ≤ _
  rw [heq, norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_mul, norm_star]
  exact (mul_le_mul (quadraticRow_norm_le_one D _) (quadraticRow_norm_le_one E _)
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem original_rectangular_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (a : n → ℂ) (b : p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, originalBlock rows left right a b D E) ^ 2 ≤
      (∑ D ∈ S, ∑ E ∈ T, quotientBlock rows left right a b D E) ^ 2 := by
  apply pow_le_pow_left₀
  · exact Finset.sum_nonneg (fun D _ => Finset.sum_nonneg (fun E _ =>
      blockValue_nonneg left right _ _ a b D E))
  · apply Finset.sum_le_sum
    intro D hD
    exact Finset.sum_le_sum (fun E hE => originalBlock_le_quotientBlock
      rows left right hleft hright a b D E)

theorem canonical_original_divisor_block_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, originalBlock rows left right a b D E) ^ 2 ≤
      256 ^ 2 * D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
        (supportConstant ε hε * divisorConstant ε hε) ^ 2 * (N ^ ε) ^ 4 *
        (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2) := by
  exact (original_rectangular_bound S T rows left right
    (fun j => (hleft j).1) (fun k => (hright k).1) a b).trans
      (canonical_divisor_block_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
        rows left right hr hl hri hrows hleft hright a b)

end CanonicalQuadraticSieve

namespace FiniteSieveRestriction
open FiniteSieveOperator

theorem squared_norm_row_partition {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) (P : m → Prop) [DecidablePred P] :
    ‖operator A‖ ^ 2 ≤
      ‖operator (fun (i : {i : m // P i}) j => A i.val j)‖ ^ 2 +
      ‖operator (fun (i : {i : m // ¬ P i}) j => A i.val j)‖ ^ 2 := by
  apply squared_norm_le_of_energy _ _ (by positivity)
  intro a
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i => ‖∑ j, A i j * a j‖ ^ 2)]
  have h₁ := energy_bound (fun (i : {i : m // P i}) j => A i.val j) a
  have h₂ := energy_bound (fun (i : {i : m // ¬ P i}) j => A i.val j) a
  exact (add_le_add h₁ h₂).trans_eq (by ring)
end FiniteSieveRestriction

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss
open QuadraticSquarefreeKernel FiniteSieveOperator

def Supported (I : Ideal O) : Prop :=
  I ≠ 0 ∧ ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
    lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2

def fullRange (M : ℝ) : Finset (Ideal O) := (idealsUpTo ⌊M⌋₊).filter Supported

theorem mem_fullRange {M : ℝ} {I : Ideal O} :
    I ∈ fullRange M ↔ Supported I ∧ (Ideal.absNorm I : ℝ) ≤ M := by
  rw [fullRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, ha⟩
    refine ⟨ha, ?_⟩
    have hM : 0 ≤ M := by
      by_contra hn
      have hz : ⌊M⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hM)
  · rintro ⟨ha, hN⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => ha.1 (Ideal.absNorm_eq_zero_iff.mp h)),
      Nat.le_floor hN⟩, ha⟩

theorem admissible_supported {I : Ideal O} (hI : Admissible I) : Supported I :=
  ⟨hI.1, hI.2.2⟩

theorem squarefreePart_eq_self {I : Ideal O} (hI : Squarefree I) : squarefreePart I = I := by
  have h := (squarePart_mul_squarefree (show (1 : Ideal O) ≠ 0 from one_ne_zero) hI).2
  simpa only [one_pow, one_mul] using h

def highKernelRange (M K : ℝ) : Finset (Ideal O) :=
  (fullRange M).filter (fun I => K < (Ideal.absNorm (squarefreePart I) : ℝ))

theorem mem_highKernelRange {M K : ℝ} {I : Ideal O} :
    I ∈ highKernelRange M K ↔
      Supported I ∧ (Ideal.absNorm I : ℝ) ≤ M ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) := by
  simp only [highKernelRange, Finset.mem_filter, mem_fullRange, and_assoc]

def highKernelMatrix (M N K : ℝ) : Matrix (highKernelRange M K) (idealRange N) ℂ :=
  fun I J => quadraticRow J.val (primaryGenerator I.val)

def highKernelNorm (M N K : ℝ) : ℝ := ‖operator (highKernelMatrix M N K)‖ ^ 2

theorem highKernelNorm_nonneg (M N K : ℝ) : 0 ≤ highKernelNorm M N K := sq_nonneg _

theorem sieveNorm_le_low_add_high (M N K : ℝ) :
    sieveNorm M N ≤ sieveNorm K N + highKernelNorm M N K := by
  let P : idealRange M → Prop := fun I => (Ideal.absNorm I.val : ℝ) ≤ K
  let lo := {I : idealRange M // P I}
  let hi := {I : idealRange M // ¬ P I}
  have hlo : ‖operator (fun (I : lo) (J : idealRange N) => matrix M N I.val J)‖ ^ 2 ≤
      sieveNorm K N := by
    apply family_squared_norm_le (fun I : lo => I.val.val) (fun J : idealRange N => J.val)
    · intro I J h
      apply Subtype.ext
      exact Subtype.ext h
    · exact Subtype.val_injective
    · intro I
      exact ⟨(mem_idealRange.mp I.val.property).1, I.property⟩
    · intro J
      exact mem_idealRange.mp J.property
  let toHigh : hi → highKernelRange M K := fun I => ⟨I.val.val, by
    apply mem_highKernelRange.mpr
    have hI := mem_idealRange.mp I.val.property
    refine ⟨admissible_supported hI.1, hI.2, ?_⟩
    rw [squarefreePart_eq_self hI.1.2.1]
    exact lt_of_not_ge I.property⟩
  have hhighinj : Function.Injective toHigh := by
    intro I J h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : highKernelRange M K => I.val) h
  have hhi := FiniteSieveRestriction.submatrix_norm_le toHigh hhighinj
    (fun J : idealRange N => J) Function.injective_id (highKernelMatrix M N K)
  have hhisq : ‖operator (fun (I : hi) (J : idealRange N) => matrix M N I.val J)‖ ^ 2 ≤
      highKernelNorm M N K := pow_le_pow_left₀ (norm_nonneg _) hhi 2
  exact (FiniteSieveRestriction.squared_norm_row_partition (matrix M N) P).trans (add_le_add hlo hhisq)

end CanonicalQuadraticSieve

open MeasureTheory
open scoped BigOperators Classical SchwartzMap
namespace QuadraticKernelTransfer
open FourierBridge EisensteinSchwartzPoisson

theorem sum_norm_integral_bound {ι : Type*} [Fintype ι]
    (b : ℝ → ℂ) (φ : ι → ℝ → ℂ) (H : ℝ)
    (hint : ∀ i, Integrable (fun t => b t * φ i t))
    (hb : Integrable (fun t => ‖b t‖))
    (hφ : ∀ t, (∑ i, ‖φ i t‖) ≤ H) :
    (∑ i, ‖∫ t, b t * φ i t‖) ≤ H * ∫ t, ‖b t‖ := by
  calc
    _ ≤ ∑ i, ∫ t, ‖b t * φ i t‖ := Finset.sum_le_sum (fun i _ => norm_integral_le_integral_norm _)
    _ = ∫ t, ∑ i, ‖b t * φ i t‖ := (integral_finsetSum _ (fun i _ => (hint i).norm)).symm
    _ ≤ ∫ t, H * ‖b t‖ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => by positivity)) (hb.const_mul H)
      filter_upwards [] with t
      simp only [norm_mul, ← Finset.mul_sum]
      calc
        _ ≤ ‖b t‖ * H := mul_le_mul_of_nonneg_left (hφ t) (norm_nonneg _)
        _ = _ := mul_comm _ _
    _ = _ := integral_const_mul _ _

theorem radial_two_variable_window (W : 𝓢(ℝ, ℂ))
    (L₁ L₂ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ x y : ℝ, |x| ≤ L₁ → |y| ≤ L₂ →
        paperRadialFourier W (R * Real.exp (x+y)) =
          ∫ t, logPhase t x * logPhase t y * b t) ∧
      (1 + R) ^ A * (∫ t, ‖b t‖) ≤ C := by
  let V₁ : ℝ → ℂ := fun x => if |x| ≤ L₁ then 1 else 0
  let V₂ : ℝ → ℂ := fun x => if |x| ≤ L₂ then 1 else 0
  let V : Bool → ℝ → ℂ := fun j => if j then V₂ else V₁
  let lengthScale : Bool → ℝ := fun j => if j then L₂ else L₁
  have hL : ∀ j, 0 ≤ lengthScale j := by intro j; cases j <;> assumption
  have hV : ∀ j x, V j x ≠ 0 → |x| ≤ lengthScale j := by
    intro j x h
    cases j
    · change |x| ≤ L₁
      change (if |x| ≤ L₁ then (1 : ℂ) else 0) ≠ 0 at h
      by_contra hx
      exact h (by simp [hx])
    · change |x| ≤ L₂
      change (if |x| ≤ L₂ then (1 : ℂ) else 0) ≠ 0 at h
      by_contra hx
      exact h (by simp [hx])
  obtain ⟨C, hC, hs⟩ := paperRadialFourier_log_separation_envelope W V (fun _ => 1) lengthScale hL hV A 0
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, _, hmass, _⟩ := hs R hR
  refine ⟨b, ?_, ?_⟩
  · intro x y hx hy
    have h := hb (fun j => if j then y else x)
    simpa only [V, V₁, V₂, lengthScale, Fintype.prod_bool, Fintype.sum_bool,
      Bool.false_eq_true, ↓reduceIte, if_pos hx, if_pos hy, one_mul, mul_one,
      add_comm, mul_comm, mul_left_comm, mul_assoc] using h
  · simpa only [pow_zero, one_mul] using hmass

theorem radial_phase_integrable (b : 𝓢(ℝ, ℂ)) (c : ℂ) (x y : ℝ) :
    Integrable (fun t => b t * (logPhase t x * (c * logPhase t y))) := by
  apply (b.integrable.norm.mul_const ‖c‖).mono'
  · have hx := logPhase_continuous_left x
    have hy := logPhase_continuous_left y
    exact (by fun_prop : Continuous (fun t => b t * (logPhase t x * (c * logPhase t y)))).aestronglyMeasurable
  · filter_upwards [] with t
    simp only [norm_mul, logPhase_norm, one_mul, mul_one]
    exact le_rfl

theorem radial_matrix_kernel_transfer (W : 𝓢(ℝ, ℂ))
    (L₁ L₂ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n : Type*} [Fintype m] [Fintype n]
        (c : m → n → ℂ) (x : m → ℝ) (y : n → ℝ) (H : ℝ),
        0 ≤ H → (∀ i, |x i| ≤ L₁) → (∀ j, |y j| ≤ L₂) →
        (∀ t, (∑ i, ‖∑ j, c i j * logPhase t (y j)‖) ≤ H) →
        (1 + R) ^ A * (∑ i, ‖∑ j, c i j *
          paperRadialFourier W (R * Real.exp (x i + y j))‖) ≤ C * H := by
  obtain ⟨C, hC, hs⟩ := radial_two_variable_window W L₁ L₂ hL₁ hL₂ A
  refine ⟨C, hC, ?_⟩
  intro R hR m n _ _ c x y H hH hx hy hphase
  obtain ⟨b, hb, hmass⟩ := hs R hR
  let φ : m → ℝ → ℂ := fun i t => logPhase t (x i) * ∑ j, c i j * logPhase t (y j)
  have hint (i : m) : Integrable (fun t => b t * φ i t) := by
    have h := integrable_finsetSum (Finset.univ : Finset n)
      (fun j _ => radial_phase_integrable b (c i j) (x i) (y j))
    simpa only [φ, Finset.mul_sum] using h
  have hid (i : m) : (∑ j, c i j * paperRadialFourier W (R * Real.exp (x i + y j))) =
      ∫ t, b t * φ i t := by
    rw [show (fun t => b t * φ i t) = fun t =>
      ∑ j, b t * (logPhase t (x i) * (c i j * logPhase t (y j))) by
        funext t; simp only [φ, Finset.mul_sum]]
    rw [integral_finsetSum _ (fun j _ => radial_phase_integrable b (c i j) (x i) (y j))]
    apply Finset.sum_congr rfl
    intro j _
    rw [hb _ _ (hx i) (hy j), ← integral_const_mul]
    congr 1
    funext t
    ring
  have hp (t : ℝ) : (∑ i, ‖φ i t‖) ≤ H := by
    simpa only [φ, norm_mul, logPhase_norm, one_mul] using hphase t
  have hi := sum_norm_integral_bound b φ H hint b.integrable.norm hp
  simp only [← hid] at hi
  calc
    _ ≤ (1 + R) ^ A * (H * ∫ t, ‖b t‖) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = H * ((1 + R) ^ A * ∫ t, ‖b t‖) := by ring
    _ ≤ H * C := mul_le_mul_of_nonneg_left hmass hH
    _ = _ := mul_comm _ _

end QuadraticKernelTransfer

namespace CanonicalQuadraticSieve
open FourierBridge EisensteinSchwartzPoisson QuadraticKernelTransfer
open IdealCoprimeSieveOperator DivisorBlockCauchy IdealDivisorBilinearBlocks

section
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def quotientTerm (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  if IsCoprime (left j) (right k) then
    star (quotientMatrix D rows left i j * (if D ∣ left j then a j else 0)) *
      (quotientMatrix E rows right i k * (if E ∣ right k then b k else 0)) else 0

def divisorBlockCost (ε : ℝ) (hε : 0 < ε) (D₁ D₂ M N : ℝ) (a : n → ℂ) (b : p → ℂ) : ℝ :=
  256 ^ 2 * D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
    (supportConstant ε hε * divisorConstant ε hε) ^ 2 * (N ^ ε) ^ 4 *
    (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2)

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem quotientTerm_phase (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p)
    (y : n → ℝ) (z : p → ℝ) (t : ℝ) :
    quotientTerm rows left right (fun j => a j * star (logPhase t (y j)))
      (fun k => b k * logPhase t (z k)) D E i j k =
    quotientTerm rows left right a b D E i j k * logPhase t (y j + z k) := by
  unfold quotientTerm
  rw [logPhase_add]
  by_cases hc : IsCoprime (left j) (right k) <;>
    by_cases hD : D ∣ left j <;> by_cases hE : E ∣ right k <;>
      simp only [hc, hD, hE, ↓reduceIte, mul_zero, zero_mul, star_zero, star_mul, star_star] ; ring

theorem canonical_divisor_block_phase_bound
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (y : n → ℝ) (z : p → ℝ) (t : ℝ) :
    (∑ D ∈ S, ∑ E ∈ T, ∑ i,
      ‖∑ j, ∑ k, quotientTerm rows left right a b D E i j k * logPhase t (y j + z k)‖) ≤
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
  have hb := canonical_divisor_block_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright
    (fun j => a j * star (logPhase t (y j))) (fun k => b k * logPhase t (z k))
  simp only [norm_mul, norm_star, logPhase_norm, mul_one] at hb
  change (∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k,
    quotientTerm rows left right (fun j => a j * star (logPhase t (y j)))
      (fun k => b k * logPhase t (z k)) D E i j k‖) ^ 2 ≤
    divisorBlockCost ε hε D₁ D₂ M N a b at hb
  simp only [quotientTerm_phase] at hb
  have hcost : 0 ≤ divisorBlockCost ε hε D₁ D₂ M N a b := (sq_nonneg _).trans hb
  have hs := Real.sq_sqrt hcost
  have hp := Real.sqrt_nonneg (divisorBlockCost ε hε D₁ D₂ M N a b)
  have hsum : 0 ≤ ∑ D ∈ S, ∑ E ∈ T, ∑ i,
      ‖∑ j, ∑ k, quotientTerm rows left right a b D E i j k * logPhase t (y j + z k)‖ := by positivity
  nlinarith
end

theorem canonical_radial_divisor_block_bound
    (W : 𝓢(ℝ, ℂ)) (L₁ L₂ L₃ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ M N : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hN : 1 ≤ N)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
        (_hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
        (_hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (x : S → T → m → ℝ) (y : n → ℝ) (z : p → ℝ),
        (∀ D E i, |x D E i| ≤ L₁) → (∀ j, |y j| ≤ L₂) → (∀ k, |z k| ≤ L₃) →
        (1 + R) ^ A * (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
          quotientTerm rows left right a b D.val E.val i j k *
            paperRadialFourier W (R * Real.exp (x D E i + (y j + z k)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
  obtain ⟨C, hC, hker⟩ := radial_matrix_kernel_transfer W L₁ (L₂ + L₃) hL₁ (add_nonneg hL₂ hL₃) A
  refine ⟨C, hC, ?_⟩
  intro R hR m n p _ _ _ _ _ _ ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright a b x y z hx hy hz
  let c : (S × T × m) → (n × p) → ℂ := fun i j =>
    quotientTerm rows left right a b i.1.val i.2.1.val i.2.2 j.1 j.2
  have hp (t : ℝ) : (∑ i : S × T × m, ‖∑ j : n × p, c i j * logPhase t (y j.1 + z j.2)‖) ≤
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
    have hb := canonical_divisor_block_phase_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
      rows left right hr hl hri hrows hleft hright a b y z t
    simp only [c, Fintype.sum_prod_type]
    let v : Ideal O → Ideal O → ℝ := fun D E => ∑ i,
      ‖∑ j, ∑ k, quotientTerm rows left right a b D E i j k * logPhase t (y j + z k)‖
    change (∑ D : S, ∑ E : T, v D.val E.val) ≤ _
    rw [Finset.sum_coe_sort S (fun D => ∑ E : T, v D E.val)]
    have he (D : Ideal O) := Finset.sum_coe_sort T (v D)
    simp_rw [he]
    exact hb
  have hb := hker R hR c (fun i => x i.1 i.2.1 i.2.2) (fun j => y j.1 + z j.2)
    (Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b)) (Real.sqrt_nonneg _)
    (fun i => hx i.1 i.2.1 i.2.2)
    (fun j => (abs_add_le _ _).trans (add_le_add (hy j.1) (hz j.2))) hp
  simpa only [c, Fintype.sum_prod_type] using hb

end CanonicalQuadraticSieve

open MeasureTheory
open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open FourierBridge EisensteinSchwartzPoisson QuadraticKernelTransfer
open IdealCoprimeSieveOperator DivisorBlockCauchy IdealDivisorBilinearBlocks

section
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalTerm (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  if IsCoprime (left j) (right k) then
    star (quadraticRow (left j) (CompletedGauss.primaryGenerator (rows i)) * (if D ∣ left j then a j else 0)) *
      (quadraticRow (right k) (CompletedGauss.primaryGenerator (rows i)) * (if E ∣ right k then b k else 0)) else 0

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalTerm_phase (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p)
    (y : n → ℝ) (z : p → ℝ) (t : ℝ) :
    originalTerm rows left right (fun j => a j * star (logPhase t (y j)))
      (fun k => b k * logPhase t (z k)) D E i j k =
    originalTerm rows left right a b D E i j k * logPhase t (y j + z k) := by
  unfold originalTerm
  rw [logPhase_add]
  by_cases hc : IsCoprime (left j) (right k) <;>
    by_cases hD : D ∣ left j <;> by_cases hE : E ∣ right k <;>
      simp only [hc, hD, hE, ↓reduceIte, mul_zero, zero_mul, star_zero, star_mul, star_star] ; ring

theorem canonical_original_divisor_block_phase_bound
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (y : n → ℝ) (z : p → ℝ) (t : ℝ) :
    (∑ D ∈ S, ∑ E ∈ T, ∑ i,
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * logPhase t (y j + z k)‖) ≤
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
  have hb := canonical_original_divisor_block_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright
    (fun j => a j * star (logPhase t (y j))) (fun k => b k * logPhase t (z k))
  simp only [norm_mul, norm_star, logPhase_norm, mul_one] at hb
  change (∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k,
    originalTerm rows left right (fun j => a j * star (logPhase t (y j)))
      (fun k => b k * logPhase t (z k)) D E i j k‖) ^ 2 ≤
    divisorBlockCost ε hε D₁ D₂ M N a b at hb
  simp only [originalTerm_phase] at hb
  have hcost : 0 ≤ divisorBlockCost ε hε D₁ D₂ M N a b := (sq_nonneg _).trans hb
  have hs := Real.sq_sqrt hcost
  have hp := Real.sqrt_nonneg (divisorBlockCost ε hε D₁ D₂ M N a b)
  have hsum : 0 ≤ ∑ D ∈ S, ∑ E ∈ T, ∑ i,
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * logPhase t (y j + z k)‖ := by positivity
  nlinarith
end

theorem canonical_original_radial_divisor_block_bound
    (W : 𝓢(ℝ, ℂ)) (L₁ L₂ L₃ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ M N : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hN : 1 ≤ N)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
        (_hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
        (_hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (x : S → T → m → ℝ) (y : n → ℝ) (z : p → ℝ),
        (∀ D E i, |x D E i| ≤ L₁) → (∀ j, |y j| ≤ L₂) → (∀ k, |z k| ≤ L₃) →
        (1 + R) ^ A * (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
          originalTerm rows left right a b D.val E.val i j k *
            paperRadialFourier W (R * Real.exp (x D E i + (y j + z k)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
  obtain ⟨C, hC, hker⟩ := radial_matrix_kernel_transfer W L₁ (L₂ + L₃) hL₁ (add_nonneg hL₂ hL₃) A
  refine ⟨C, hC, ?_⟩
  intro R hR m n p _ _ _ _ _ _ ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright a b x y z hx hy hz
  let c : (S × T × m) → (n × p) → ℂ := fun i j =>
    originalTerm rows left right a b i.1.val i.2.1.val i.2.2 j.1 j.2
  have hp (t : ℝ) : (∑ i : S × T × m, ‖∑ j : n × p, c i j * logPhase t (y j.1 + z j.2)‖) ≤
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
    have hb := canonical_original_divisor_block_phase_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
      rows left right hr hl hri hrows hleft hright a b y z t
    simp only [c, Fintype.sum_prod_type]
    let v : Ideal O → Ideal O → ℝ := fun D E => ∑ i,
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * logPhase t (y j + z k)‖
    change (∑ D : S, ∑ E : T, v D.val E.val) ≤ _
    rw [Finset.sum_coe_sort S (fun D => ∑ E : T, v D E.val)]
    have he (D : Ideal O) := Finset.sum_coe_sort T (v D)
    simp_rw [he]
    exact hb
  have hb := hker R hR c (fun i => x i.1 i.2.1 i.2.2) (fun j => y j.1 + z j.2)
    (Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b)) (Real.sqrt_nonneg _)
    (fun i => hx i.1 i.2.1 i.2.2)
    (fun j => (abs_add_le _ _).trans (add_le_add (hy j.1) (hz j.2))) hp
  simpa only [c, Fintype.sum_prod_type] using hb

end CanonicalQuadraticSieve

end

end OAI

end



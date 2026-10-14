-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0113
-- name    : PNT_ZeroFree_433_0113
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:27:25.177677+00:00
-- url     : https://prove2.me/theorems/796e421e-05b4-498b-9e9d-bd66fa2b421c
-- title:
--   Zero-free region foundations: QuadraticSieve.DualMiddleExpansion [0113]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.DualMiddleExpansion
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/DualMiddleExpansion.lean#L78-L731

import Definitions.Def_PNT_ZeroFree_433_0112

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/DualMiddleExpansion.lean#L78-L731
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.DualMiddleExpansion
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem scaled_middleTruncation_eq_ideal_frequencies (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (c X Y Z lengthScale : ℝ) :
    (c : ℂ) * middleTruncation (fun P : primePool {G} => P.val) Finset.univ W X Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            ((((c * X) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  classical
  rw [middleTruncation_eq_ideal_frequencies G hG]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z
  · simp only [hp, and_self, ite_true]
    push_cast
    ring
  · simp only [hp, ite_false, mul_zero]

theorem dual_normalized_middle_expansion (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (M F b i j Y Z lengthScale : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hi : 0 < i) (hj : 0 < j) :
    ((M / (Real.sqrt (i * j) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primePool {G} => P.val) Finset.univ W
        (Real.sqrt (F * i * j / (M * b))) Y Z lengthScale =
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, ∑ d ∈ idealDivisors G,
        if Y < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z then
          (UniqueFactorizationMonoid.moebius d : ℂ) *
            (((Real.sqrt ((M / F) / b) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
              paperRadialFourier W
                (Real.sqrt (F * i * j / (M * b)) * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm d : ℝ)))
        else 0 := by
  rw [scaled_middleTruncation_eq_ideal_frequencies G hG,
    dual_principal_prefactor_identity M F b i j hM hF hb hi hj]

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def dualTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ)))) (Y i) (Z i) lengthScale)

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dual_truncated_pair_expansion
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hrows : ∀ i, Admissible (rows i))
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) (i : m) (j : n) (k : p) :
    originalTerm rows left right a b 1 1 i j k *
      (((M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) : ℂ) *
        middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
          (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
            (M * (Ideal.absNorm (rows i) : ℝ)))) (Y i) (Z i) lengthScale) =
      ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val : ℂ) *
        (if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
          if d.val ∣ left j * right k then
            originalTerm rows left right a b 1 1 i j k *
              dualPrincipalKernel W rows left right M F h.val d.val i j k
          else 0 else 0) := by
  classical
  rw [sum_two_finite_subtypes (rowNormDisk ⌊lengthScale⌋₊) K (fun h d =>
    (UniqueFactorizationMonoid.moebius d : ℂ) *
      (if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
        if d ∣ left j * right k then
          originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k
        else 0 else 0))]
  by_cases hc : IsCoprime (left j) (right k)
  · have hsq : Squarefree (left j * right k) :=
      squarefree_mul_iff.mpr ⟨hc.isRelPrime, (hleft j).2.1, (hright k).2.1⟩
    have hpos (I : Ideal O) (hI : Admissible I) : 0 < (Ideal.absNorm I : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => hI.1 (Ideal.absNorm_eq_zero_iff.mp h))
    rw [dual_normalized_middle_expansion _ hsq _ _ _ _ _ _ _ _ _ hM hF
      (hpos _ (hrows i)) (hpos _ (hleft j)) (hpos _ (hright k)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    rw [← divisorPool_filter K (left j * right k) hsq.ne_zero (hK j k), Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdv : d ∣ left j * right k
    · by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
      · simp only [hdv, hp, and_self, ite_true, dualPrincipalKernel]
        ring
      · simp only [hdv, hp, ite_true, ite_false, mul_zero]
    · simp only [hdv, ite_false, ite_self, mul_zero]
  · have hz : originalTerm rows left right a b 1 1 i j k = 0 := by simp only [originalTerm, hc, ite_false]
    simp only [hz, zero_mul, ite_self, mul_zero, Finset.sum_const_zero]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualTruncatedMiddle_le_product_divisors
    (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hrows : ∀ i, Admissible (rows i))
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hK : ∀ j k d, d ∣ left j * right k → d ∈ K) :
    ‖dualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, dualProductDivisorMiddleAt W K rows left right a b M F
        (fun d i => Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i) h := by
  classical
  let A : m → n → p → rowNormDisk ⌊lengthScale⌋₊ → K → ℂ := fun i j k h d =>
    if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h.val d.val i j k
      else 0 else 0
  have he : dualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ∑ i, ∑ j, ∑ k, ∑ h : rowNormDisk ⌊lengthScale⌋₊, ∑ d : K,
        (UniqueFactorizationMonoid.moebius d.val : ℂ) * A i j k h d := by
    unfold dualTruncatedMiddle
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    exact dual_truncated_pair_expansion W K rows left right a b M F Y Z lengthScale hM hF hrows hleft hright hK i j k
  rw [he]
  apply (finite_middle_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val : ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans_eq
  rw [Finset.sum_coe_sort (rowNormDisk ⌊lengthScale⌋₊) (fun h => ∑ i, ∑ d : K,
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d.val : ℝ) ∧ (Ideal.absNorm d.val : ℝ) ≤ Z i then
      if d.val ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d.val i j k
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro h hh
  unfold dualProductDivisorMiddleAt
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_coe_sort K (fun d =>
    ‖∑ j, ∑ k, if Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i then
      if d ∣ left j * right k then
        originalTerm rows left right a b 1 1 i j k * dualPrincipalKernel W rows left right M F h d i j k
      else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hp : Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i <;>
    simp only [hp, and_self, ite_true, ite_false, Finset.sum_const_zero, norm_zero]

theorem HasSieveExponent.dual_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    ‖dualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  let pairCols : n × p → Ideal O := fun x => left x.1 * right x.2
  let K := columnDivisorPool pairCols
  have hPair : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hleft x.1).1.1 (hright x.2).1.1
  have hK (j : n) (k : p) (d : Ideal O) (hd : d ∣ left j * right k) : d ∈ K :=
    mem_columnDivisorPool_of_dvd pairCols hPair (j, k) d hd
  let P : Ideal O → m → Prop := fun d i =>
    Y i < (Ideal.absNorm d : ℝ) ∧ (Ideal.absNorm d : ℝ) ≤ Z i
  have hb := hexp.dual_product_divisor_middle deltaLoss hδ ε hε K B N M F U hB hN hM hF hU
    rows left right hr hl hri hrows a b (fun _ => a) (fun _ => b)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) W P hleft hright
    (fun d hd i hp => hp.2.trans (hZ i))
  have hH (h : O) (hh : h ∈ rowNormDisk ⌊lengthScale⌋₊) : h ≠ 0 := by
    intro hz
    have hn := (mem_rowNormDisk.mp hh).1
    simp [hz] at hn
  calc
    _ ≤ ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, dualProductDivisorMiddleAt W K rows left right a b M F P h :=
      dualTruncatedMiddle_le_product_divisors W K rows left right a b M F Y Z lengthScale hM hF (fun i => (hrows i).1)
        (fun j => (hleft j).1) (fun k => (hright k).1) hK
    _ ≤ ∑' h : {h : O // h ≠ 0}, dualProductDivisorMiddleAt W K rows left right a b M F P h.val :=
      finite_nonzero_frequency_sum_le (rowNormDisk ⌊lengthScale⌋₊) hH _
        (fun h => dualProductDivisorMiddleAt_nonneg W K rows left right a b M F P h) hb.1
    _ ≤ _ := hb.2

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel primeProduct bit)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hcop in
omit [DecidableEq ι] in
theorem primeSpanProduct_squarefree (S : Finset ι) :
    Squarefree (∏ i ∈ S, Ideal.span {p i}) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact (hcop hij).isRelPrime
  · intro i hi
    exact (Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance).squarefree

omit [DecidableEq ι] in
theorem row_nonzero_notMem (S : Finset ι) (c : O)
    (h : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c ≠ 0) :
    ∀ i ∈ S, c ∉ Ideal.span {p i} := by
  intro i hi hc
  have hzero : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c ^ 6 = 0 := by
    rw [← FirstPassCubeLabels.row_pow, finiteSquarefreeRow_sixth_power, if_pos ⟨i,hi,hc⟩]
  exact pow_ne_zero 6 h hzero

omit [DecidableEq ι] in
theorem primeSpanProduct_isCoprime_of_row_nonzero (S : Finset ι) (c : O)
    (h : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c ≠ 0) :
    IsCoprime (∏ i ∈ S, Ideal.span {p i}) (Ideal.span {c}) := by
  apply IsCoprime.prod_left
  intro i hi
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra htop
  have he := Ideal.IsMaximal.eq_of_le (inferInstance : (Ideal.span {p i}).IsMaximal)
    htop (show Ideal.span {p i} ≤ Ideal.span {p i} ⊔ Ideal.span {c} from le_sup_left)
  have hc : c ∈ Ideal.span {p i} := by
    rw [he]
    exact (show Ideal.span {c} ≤ Ideal.span {p i} ⊔ Ideal.span {c} from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton c))
  exact row_nonzero_notMem p hg S c h i hi hc

def firstRetainedSupport (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  B.filter (fun i => FirstPassCubeLabels.retained (FirstPassCubeLabels.parity (v i)) (ε₁ i) (ε₂ i))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem jLabel_eq_retainedProduct (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    jLabel p B v ε₁ ε₂ = ∏ i ∈ firstRetainedSupport B v ε₁ ε₂, p i := by
  unfold jLabel primeProduct firstRetainedSupport
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  cases hb : FirstPassCubeLabels.retained (FirstPassCubeLabels.parity (v i)) (ε₁ i) (ε₂ i) <;> simp [bit,hb]

include hcop in
theorem firstBaseLabel_squarefree (B C : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hCB : Disjoint C B) :
    Squarefree (Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B v ε₁ ε₂}) := by
  have hCJ : Disjoint C (firstRetainedSupport B v ε₁ ε₂) :=
    Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hCB
  rw [← Ideal.span_singleton_mul_span_singleton, jLabel_eq_retainedProduct,
    FiniteGaussPhase.span_finset_prod, primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator,
    ← Finset.prod_union hCJ]
  exact primeSpanProduct_squarefree p hcop _

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondArithmeticWeight (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (x : SecondExpansionData ι) : ℂ :=
  secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor *
    secondTotalWeight p hp hcop hg Ψ Ψ m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (z,x.overlap)

theorem secondArithmeticWeight_coprime (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (h : secondArithmeticWeight p hp hcop hg Ψ m c d z x ≠ 0) :
    IsCoprime (Ideal.span {c}) (∏ i ∈ x.divisor, Ideal.span {p i}) ∧
    IsCoprime (Ideal.span {c}) (∏ i ∈ x.overlap, Ideal.span {p i}) ∧
    IsCoprime (∏ i ∈ x.divisor, Ideal.span {p i}) (∏ i ∈ x.overlap, Ideal.span {p i}) := by
  have hG : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg x.sourceCommon c ≠ 0 := by
    intro hz
    apply h
    simp only [secondArithmeticWeight, secondSourceCommonCoefficient, secondInputCoefficient,
      hz, zero_pow (by decide : 4 ≠ 0), mul_zero, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Complex.ofReal_zero]
  have hV : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg x.overlap c ≠ 0 := by
    intro hz
    apply h
    simp only [secondArithmeticWeight, secondTotalWeight, secondCommonWeight, secondPreColumn,
      hz, zero_pow (by decide : 4 ≠ 0), mul_zero, zero_mul, star_zero]
  have hVe : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg x.overlap
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) ≠ 0 := by
    intro hz
    apply h
    simp only [secondArithmeticWeight, secondTotalWeight, secondCommonWeight, secondPreColumn,
      hz, mul_zero, zero_mul, star_zero]
  have hGc := primeSpanProduct_isCoprime_of_row_nonzero p hg x.sourceCommon c hG
  have hEc : IsCoprime (∏ i ∈ x.divisor, Ideal.span {p i}) (Ideal.span {c}) := by
    apply IsCoprime.prod_left
    intro i hi
    exact (IsCoprime.prod_left_iff.mp hGc) i (hE hi)
  have hVc := primeSpanProduct_isCoprime_of_row_nonzero p hg x.overlap c hV
  have hVE := primeSpanProduct_isCoprime_of_row_nonzero p hg x.overlap _ hVe
  rw [primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator] at hVE
  exact ⟨hEc.symm,hVc.symm,hVE.symm⟩

theorem secondArithmeticWeight_squarefree (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (hc : Squarefree (Ideal.span {c}))
    (h : secondArithmeticWeight p hp hcop hg Ψ m c d z x ≠ 0) :
    Squarefree (Ideal.span {c} * (∏ i ∈ x.divisor, Ideal.span {p i}) *
      (∏ i ∈ x.overlap, Ideal.span {p i})) := by
  obtain ⟨hcE,hcV,hEV⟩ := secondArithmeticWeight_coprime p hp hcop hg Ψ m c d z x hE h
  apply squarefree_mul_iff.mpr
  refine ⟨(hcV.mul_left hEV).isRelPrime,?_,primeSpanProduct_squarefree p hcop _⟩
  exact squarefree_mul_iff.mpr ⟨hcE.isRelPrime,hc,primeSpanProduct_squarefree p hcop _⟩

theorem actualSecondLabel_squarefree_of_weight
    (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hCB : Disjoint C B)
    (Ψ : O →* ℂ) (m d : O) (z : SecondRayIndex)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (h : secondArithmeticWeight p hp hcop hg Ψ m
      (primeSubsetGenerator (fun i => Ideal.span {p i}) C *
        jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂) d z x ≠ 0) :
    Squarefree (actualSecondLabel p B C x.divisor x.overlap v₁ v₂ ε₁ ε₂) := by
  have hs := secondArithmeticWeight_squarefree p hp hcop hg Ψ m _ d z x hE
    (firstBaseLabel_squarefree p hcop B C (fun i => v₁ i+v₂ i) ε₁ ε₂ hCB) h
  rw [← Ideal.span_singleton_mul_span_singleton, primeSubsetGenerator,
    ConcretePrimeRowBridge.span_idealGenerator, mul_comm (∏ i ∈ C, Ideal.span {p i})] at hs
  exact hs

theorem secondExpansionSource_eq_squarefree
    (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hCB : Disjoint C B)
    (F : Finset ι) (Ψ : O →* ℂ) (m d : O) (z : SecondRayIndex)
    (s : Finset (SecondExpansionData ι)) (hE : ∀ x ∈ s, x.divisor ⊆ x.sourceCommon)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C *
      jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂
    secondExpansionSource p hp hcop hg F Ψ m c d z s H₁ H₂ W Y =
    secondExpansionSource p hp hcop hg F Ψ m c d z
      (s.filter (fun x => Squarefree (actualSecondLabel p B C x.divisor x.overlap v₁ v₂ ε₁ ε₂)))
      H₁ H₂ W Y := by
  dsimp only
  unfold secondExpansionSource
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : Squarefree (actualSecondLabel p B C x.divisor x.overlap v₁ v₂ ε₁ ε₂)
  · rw [if_pos hs]
  · rw [if_neg hs]
    have hw : secondArithmeticWeight p hp hcop hg Ψ m
        (primeSubsetGenerator (fun i => Ideal.span {p i}) C *
          jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂) d z x = 0 := by
      by_contra hn
      exact hs (actualSecondLabel_squarefree_of_weight p hp hcop hg B C v₁ v₂ ε₁ ε₂ hCB
        Ψ m d z x (hE x hx) hn)
    unfold secondArithmeticWeight at hw
    rcases mul_eq_zero.mp hw with hA | hB
    · rw [hA]
      ring
    · rw [hB]
      ring

end

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (densityChildEnergy childGeometricMean childEnergy)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondLogNormalizedEnergy (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) : ℝ :=
  densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m
    (secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) V₁ V₂
    (secondLogX p R X j) (secondLogX p R X j) J /
  (secondLogX p R X j * secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j)

lemma secondLogNormalizedEnergy_nonneg
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (hX : 0 < X)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) :
    0 ≤ secondLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J := by
  apply div_nonneg
  · apply integral_nonneg
    intro t₁
    apply integral_nonneg
    intro t₂
    apply integral_nonneg
    intro t₃
    exact mul_nonneg (JointLogSeparation.tripleLogDensity_nonneg _ _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · exact mul_nonneg (secondLogX_pos p hp R X hX j).le
      (zero_le_one.trans (secondLogLabelBound_ge_one p hp B C v₁ v₂ ε₁ ε₂ j))

lemma secondLogNormalizedEnergy_empty
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ)
    (hT : secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j = ∅) :
    secondLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J = 0 := by
  simp only [secondLogNormalizedEnergy, hT, densityChildEnergy, childGeometricMean, childEnergy,
    Finset.sum_empty, Finset.sum_const_zero, Real.sqrt_zero, mul_zero, integral_zero, zero_div]

theorem secondLog_normalized_cost
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X Y M : ℝ) (hX : 0 < X)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) :
    (Y*primeProductNorm p R/X^2) *
      densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m
        (secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) V₁ V₂
        (secondLogX p R X j) (secondLogX p R X j) J =
    (Y*‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2*Real.exp 2/X) *
      secondLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J := by
  unfold secondLogNormalizedEnergy
  rw [secondLogX_label_cost]
  have hR := (FirstPassCubeLabels.primeProductNorm_pos p hp R).ne'
  have hc := (zero_lt_one.trans_le (element_norm_ge_one _ (secondBaseLabel_ne_zero p hp B C v₁ v₂ ε₁ ε₂))).ne'
  have hcn : ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖ ≠ 0 := by
    intro h; apply hc; rw [h]; norm_num
  field_simp

include hp in

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem first_second_normalized_child_cost
    (A B C R : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (X Y : ℝ) (hX : 0 < X) (j : SecondLogIndex) :
    (primeProductNorm p A)⁻¹ *
      (Y*primeProductNorm p R/(X/primeProductNorm p A)^2) *
      (secondLogX p R (X/primeProductNorm p A) j * secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j) =
    Y*‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2*Real.exp 2/X := by
  rw [secondLogX_label_cost]
  have hA := (FirstPassCubeLabels.primeProductNorm_pos p hp A).ne'
  have hR := (FirstPassCubeLabels.primeProductNorm_pos p hp R).ne'
  field_simp

end

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem secondBinnedIndex_mass (F : Finset ι) (U Kmax : ℝ) :
    (∑ z : SecondRayIndex, ∑ _R ∈ boundedPrimeSupports p F U,
      ∑ _j ∈ secondLogBinBox U Kmax, ‖secondRayCoefficient z‖) ≤
    (512*32^2) * (128*max 1 U) *
      (((normLogBin U+1)^2*(normLogBin Kmax+1) : ℕ) : ℝ) := by
  have hsub : boundedPrimeSupports p F U ⊆ boundedPrimeSupports p F (max 1 U) := by
    intro R hR
    obtain ⟨hR,hN⟩ := Finset.mem_filter.mp hR
    exact Finset.mem_filter.mpr ⟨hR,hN.trans (le_max_right _ _)⟩
  have hc : ((boundedPrimeSupports p F U).card : ℝ) ≤ 128*max 1 U := by
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (boundedPrimeSupports_card p hinj F (max 1 U) (le_max_left _ _))
  have he : (∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F U,
      ∑ j ∈ secondLogBinBox U Kmax, ‖secondRayCoefficient z‖) =
      (∑ z : SecondRayIndex, ‖secondRayCoefficient z‖) *
        (boundedPrimeSupports p F U).card * (secondLogBinBox U Kmax).card := by
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_mul]
    ring_nf
  rw [he, secondLogBinBox_card]
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul secondRayCoefficient_mass hc (by positivity) (by positivity)
  · positivity

end SecondPassArithmetic

namespace FirstPassCubeLabels
open scoped BigOperators
open MeasureTheory

lemma firstLogDensity_pair_moment (J : ℕ) (t : ℝ) :
    firstLogDensity (2*(J+2)) t * ((1+‖t‖)^(J+2) * (1+‖t‖)^(J+2)) = firstLogDensity 0 t := by
  rw [← pow_add, show J+2+(J+2)=2*(J+2) by omega, mul_comm]
  exact JointLogSeparation.density_weight_identity _ _

lemma firstLogDensity_le_zero (J : ℕ) (t : ℝ) : firstLogDensity J t ≤ firstLogDensity 0 t := by
  have h := pow_le_pow_right₀ (show 1 ≤ 1+‖t‖ by linarith [norm_nonneg t]) (show 2 ≤ J+2 by omega)
  apply inv_anti₀ (by positivity : 0 < (1+‖t‖)^2) h

lemma integral_pair_moment_bound (J : ℕ) (f : ℝ → ℝ)
    (hf : Integrable (fun t => firstLogDensity (2*(J+2)) t * f t))
    (a d c q : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) (hq : 0 ≤ q)
    (h : ∀ t, f t ≤ a*(d + ((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*c + q)) :
    (∫ t, firstLogDensity (2*(J+2)) t * f t) ≤
      (∫ t, firstLogDensity 0 t) * a * (d+c+q) := by
  have hi := (firstLogDensity_integrable 0).mul_const (a*(d+c+q))
  have hm : ∀ t, firstLogDensity (2*(J+2)) t * f t ≤ firstLogDensity 0 t*(a*(d+c+q)) := by
    intro t
    apply (mul_le_mul_of_nonneg_left (h t) (firstLogDensity_nonneg _ _)).trans
    have h1 := mul_le_mul_of_nonneg_right (firstLogDensity_le_zero (2*(J+2)) t) (mul_nonneg ha hd)
    have h2 := mul_le_mul_of_nonneg_right (firstLogDensity_le_zero (2*(J+2)) t) (mul_nonneg ha hq)
    have he := firstLogDensity_pair_moment J t
    calc
      _ = firstLogDensity (2*(J+2)) t*(a*d) +
          (firstLogDensity (2*(J+2)) t*((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2)))*(a*c) +
          firstLogDensity (2*(J+2)) t*(a*q) := by ring
      _ ≤ firstLogDensity 0 t*(a*d) + firstLogDensity 0 t*(a*c) + firstLogDensity 0 t*(a*q) := by
        rw [he]
        exact add_le_add (add_le_add h1 le_rfl) h2
      _ = _ := by ring
  have hh := integral_mono hf hi hm
  rw [integral_mul_const] at hh
  simpa only [mul_assoc] using hh

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy)

theorem firstCoreInputRow_binned_integrated_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (tailOrder decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw Ctail : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧ 0 < Ctail ∧
      ∀ (Y : ℝ), 0 < Y →
      ∀ (A₀ B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (χ : RayCharacter) (Ψ : O →* ℂ) (m : O) (r₁ : FirstCoreIndex)
        (X Z : ℝ) (Srows : Finset O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ Z →
        (∀ z ∈ Srows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
        (∀ z ∈ Srows, z ≠ 0) →
        let v := fun i => v₁ i + v₂ i
        let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Ψ' := firstCoreTwist negative χ Ψ r₁
        let m' := m * b0Label p B v ε₁ ε₂
        let c' := c * jLabel p B v ε₁ ε₂
        let X' := X / primeProductNorm p A₀
        let Usupp := X' * Real.exp M
        let K := firstCoreSecondCutoff p A₀ X Y M Z
        let Kmax := firstCoreSecondRowBound p D A₀ X Y M Z
        let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
        (∫ t : ℝ, FirstPassCubeLabels.firstLogDensity (2*(J+2)) t * (∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
          (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ t z‖^2)) ≤
        (∫ t : ℝ, FirstPassCubeLabels.firstLogDensity 0 t) * (primeProductNorm p A₀)⁻¹ *
          (|Y| * ‖paperRadialFourier rowMajorant 0‖ *
              (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖^2) +
            (∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
              ∑ j ∈ secondLogBinBox Usupp Kmax,
              (Y * primeProductNorm p R / X'^2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
                (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j *
                  Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
              (Cₛ /
                (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
              densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
                (m' * primeSubsetGenerator (fun i => Ideal.span {p i}) R)
                (secondLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
                (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J) +
            Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder) := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,hpoint⟩ :=
    firstCoreInputRow_binned_finite_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g V negative hU M hM hgM ε hε tailOrder decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,?_⟩
  intro Y hY A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z Srows hv hCB hD hΨ hX hZ hSrows hSrows0
  dsimp only
  let v := fun i => v₁ i+v₂ i
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
  let Ψ' := firstCoreTwist negative χ Ψ r₁
  let m' := m*b0Label p B v ε₁ ε₂
  let c' := c*jLabel p B v ε₁ ε₂
  let X' := X/primeProductNorm p A₀
  let Usupp := X'*Real.exp M
  let K := firstCoreSecondCutoff p A₀ X Y M Z
  let Kmax := firstCoreSecondRowBound p D A₀ X Y M Z
  let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
  let f := fun t => ∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
    (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ t z‖^2
  let diag := |Y| * ‖paperRadialFourier rowMajorant 0‖*
    (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖^2)
  let tail := Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder
  let childAt := fun t : ℝ => ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
    ∑ j ∈ secondLogBinBox Usupp Kmax,
    (Y*primeProductNorm p R/X'^2*‖secondRayCoefficient z‖*Cw*Cₐ*
      (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j*Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
    (Cₛ*(1+‖t‖)^(J+2)*(1+‖t‖)^(J+2) /
      (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
    densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
      (m'*primeSubsetGenerator (fun i => Ideal.span {p i}) R)
      (secondLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
      (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J
  let child := ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
    ∑ j ∈ secondLogBinBox Usupp Kmax,
    (Y*primeProductNorm p R/X'^2*‖secondRayCoefficient z‖*Cw*Cₐ*
      (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j*Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
    (Cₛ /
      (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
    densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
      (m'*primeSubsetGenerator (fun i => Ideal.span {p i}) R)
      (secondLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
      (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J
  have hchild (t : ℝ) : childAt t = ((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*child := by
    dsimp only [child, childAt]
    simp only [    Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    apply Finset.sum_congr rfl
    intro R hR
    apply Finset.sum_congr rfl
    intro j hj
    ring
  change (∫ t, firstLogDensity (2*(J+2)) t*f t) ≤
    (∫ t, firstLogDensity 0 t)*(primeProductNorm p A₀)⁻¹*(diag+child+tail)
  apply FirstPassCubeLabels.integral_pair_moment_bound J f
  · dsimp only [f]
    simp only [Finset.mul_sum]
    apply integrable_finsetSum
    intro z hz
    exact firstCoreInputRow_integrable p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
      (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ z
      (FirstPassCubeLabels.firstLogDensity_integrable (2*(J+2)))
  · exact inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp A₀).le
  · dsimp [diag]
    positivity
  · dsimp [tail]
    positivity
  · intro t
    have hb := hpoint Y hY A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z t Srows
      hv hCB hD hΨ hX hZ hSrows hSrows0
    change f t + _ ≤ (primeProductNorm p A₀)⁻¹*(diag+childAt t+tail) at hb
    rw [hchild] at hb
    exact (le_add_of_nonneg_right (sq_nonneg _)).trans hb

end SecondPassArithmetic

end

end OAI

end



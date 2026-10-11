-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0031
-- name    : PNT_ZeroFree_433_0031
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T13:47:15.757298+00:00
-- url     : https://prove2.me/theorems/05fd8241-cb67-4e8d-b7e0-f69c3139ff81
-- title:
--   Zero-free region foundations: PrimeRows.NormFiberExtraction [0031]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.PrimeRows.NormFiberExtraction
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/PrimeRows/NormFiberExtraction.lean#L50-L646

import Definitions.Def_PNT_ZeroFree_433_0029

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/PrimeRows/NormFiberExtraction.lean#L50-L646
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.PrimeRows.NormFiberExtraction
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

namespace ConcretePrimeRowBridge

section

open ActualEisensteinCubic ShortDraftHeckeBridge

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

noncomputable def idealGenerator (I : Ideal O) : O :=
  Submodule.IsPrincipal.generator I

theorem span_idealGenerator (I : Ideal O) :
    Ideal.span {idealGenerator I} = I := by
  exact Submodule.IsPrincipal.span_singleton_generator I

theorem idealGenerator_injective : Function.Injective idealGenerator := by
  intro I J h
  calc
    I = Ideal.span {idealGenerator I} := (span_idealGenerator I).symm
    _ = Ideal.span {idealGenerator J} := by rw [h]
    _ = J := span_idealGenerator J

noncomputable def idealsUpTo (D : ℕ) : Finset (Ideal O) :=
  (Finset.Icc 1 D).biUnion
    (fun n => (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset)

theorem mem_idealsUpTo {D : ℕ} {I : Ideal O} :
    I ∈ idealsUpTo D ↔ 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D := by
  classical
  simp [idealsUpTo, Finset.mem_biUnion, Finset.mem_Icc]

noncomputable def columnsUpTo (D : ℕ) : Finset O :=
  by
    classical
    exact (idealsUpTo D).image idealGenerator

noncomputable def columnWeight {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (x : O) : ℂ :=
  baseChangeWeight χ (Ideal.span {x}) * W (Ideal.absNorm (Ideal.span {x}))

theorem columnWeight_idealGenerator {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (I : Ideal O) :
    columnWeight χ W (idealGenerator I) =
      baseChangeWeight χ I * W (Ideal.absNorm I) := by
  simp [columnWeight, span_idealGenerator]

theorem columnsUpTo_sum_eq_ideal_sum {q D : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) :
    (∑ x ∈ columnsUpTo D, columnWeight χ W x) =
      ∑ I ∈ idealsUpTo D,
        baseChangeWeight χ I * W (Ideal.absNorm I) := by
  classical
  rw [columnsUpTo, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    exact columnWeight_idealGenerator χ W I
  · intro I hI J hJ h
    exact idealGenerator_injective h

noncomputable def goodLambda : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1

noncomputable def primePool (F : Finset (Ideal O)) : Finset (Ideal O) :=
  F.biUnion (fun I => (UniqueFactorizationMonoid.normalizedFactors I).toFinset)

theorem mem_primePool_iff {F : Finset (Ideal O)} {P : Ideal O} :
    P ∈ primePool F ↔
      ∃ I ∈ F, P ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  simp only [primePool, Finset.mem_biUnion, Multiset.mem_toFinset]

theorem primePool_maximal (F : Finset (Ideal O))
    (_hFpos : ∀ I ∈ F, I ≠ ⊥) (i : primePool F) :
    (i.1).IsMaximal := by
  obtain ⟨I, hIF, hfac⟩ := mem_primePool_iff.mp i.property
  have hp : Prime i.1 := UniqueFactorizationMonoid.prime_of_normalized_factor i.1 hfac
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

theorem primePool_good (F : Finset (Ideal O))
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (i : primePool F) : goodLambda ∉ i.1 := by
  obtain ⟨I, hIF, hfac⟩ := mem_primePool_iff.mp i.property
  exact hFgood I hIF i.1 hfac

noncomputable def idealSupport (F : Finset (Ideal O)) (I : Ideal O) :
    Finset (primePool F) :=
  Finset.univ.filter (fun i => i.1 ∈ UniqueFactorizationMonoid.normalizedFactors I)

theorem mem_idealSupport_iff (F : Finset (Ideal O)) (I : Ideal O)
    (i : primePool F) :
    i ∈ idealSupport F I ↔ i.1 ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  simp [idealSupport]

theorem idealGenerator_mem_prime_of_support
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (I : Ideal O) (hIF : I ∈ F) (i : primePool F)
    (hi : i ∈ idealSupport F I) : idealGenerator I ∈ i.1 := by
  have hfac := (mem_idealSupport_iff F I i).mp hi
  have hle := ((Ideal.mem_normalizedFactors_iff (hFpos I hIF)).mp hfac).2
  have hmem : idealGenerator I ∈ Ideal.span {idealGenerator I} :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [span_idealGenerator I] at hmem
  exact hle hmem

noncomputable def idealSexticRow
    (F : Finset (Ideal O))
    (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (I : Ideal O) (u : O) : ℂ := by
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact ActualEisensteinCubic.finiteSquarefreeRow
    (fun i : primePool F => i.1) (primePool_good F hFgood)
    (idealSupport F I) u

theorem idealSexticRow_one
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (I : Ideal O) : idealSexticRow F hFpos hFgood I 1 = 1 := by
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact ActualEisensteinCubic.finiteSquarefreeRow_one
    (fun i : primePool F => i.1) (primePool_good F hFgood)
    (idealSupport F I)

theorem baseChangeWeight_zero_of_not_squarefree {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O)
    (hI : ¬ Squarefree I) : baseChangeWeight χ I = 0 := by
  rw [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hI]
  simp

private theorem idealMoebius_norm_le_one (I : Ideal O) :
    ‖((UniqueFactorizationMonoid.moebius I : ℤ) : ℂ)‖ ≤ 1 := by
  classical
  by_cases h : Squarefree I
  · rw [h.moebius_eq]
    simp
  · rw [UniqueFactorizationMonoid.moebius_of_not_squarefree h]
    simp

theorem baseChangeWeight_norm_le_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    ‖baseChangeWeight χ I‖ ≤ 1 := by
  rw [baseChangeWeight, norm_mul]
  have hμ := idealMoebius_norm_le_one I
  have hχ := χ.norm_le_one (Ideal.absNorm I)
  exact (mul_le_mul hμ hχ (norm_nonneg _) (by positivity)).trans (by norm_num)

theorem columnWeight_norm_le_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (hW : ∀ n, ‖W n‖ ≤ 1) (x : O) :
    ‖columnWeight χ W x‖ ≤ 1 := by
  rw [columnWeight, norm_mul]
  have hμ := baseChangeWeight_norm_le_one χ (Ideal.span {x})
  have hW' := hW (Ideal.absNorm (Ideal.span {x}))
  exact (mul_le_mul hμ hW' (norm_nonneg _) (by positivity)).trans (by norm_num)

noncomputable def elementRow
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (u : O) : ℂ := by
  classical
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact ∑ x ∈ F.image idealGenerator,
    columnWeight χ W x *
      finiteSquarefreeRow (fun i : primePool F => i.1)
        (primePool_good F hFgood)
        (idealSupport F (Ideal.span {x})) u

noncomputable def idealRowSum
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (u : O) : ℂ :=
  ∑ I ∈ F,
    baseChangeWeight χ I * W (Ideal.absNorm I) *
      idealSexticRow F hFpos hFgood I u

theorem elementRow_eq_idealRowSum
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (u : O) :
    elementRow F hFpos hFgood χ W u =
      idealRowSum F hFpos hFgood χ W u := by
  classical
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  unfold elementRow idealRowSum
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    rw [columnWeight_idealGenerator, span_idealGenerator]
    rfl
  · intro I hI J hJ h
    exact idealGenerator_injective h

theorem idealRowSum_one
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) :
    idealRowSum F hFpos hFgood χ W 1 =
      ∑ I ∈ F, baseChangeWeight χ I * W (Ideal.absNorm I) := by
  unfold idealRowSum
  apply Finset.sum_congr rfl
  intro I hI
  rw [idealSexticRow_one]
  ring

open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped Classical

noncomputable def rowNormDisk (H : ℕ) : Finset O := by
  classical
  exact (ShortDraftLatticeCount.rowNormBall H).filter
    (fun u => 0 < Ideal.absNorm (Ideal.span {u}) ∧
      Ideal.absNorm (Ideal.span {u}) ≤ H)

theorem mem_rowNormDisk {H : ℕ} {u : O} :
    u ∈ rowNormDisk H ↔
      0 < Ideal.absNorm (Ideal.span {u}) ∧
      Ideal.absNorm (Ideal.span {u}) ≤ H := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le H u h.2, h⟩

theorem sixth_power_rows_in_rowNormDisk
    {β : Type*} (selected : Finset β) (p : β → O)
    (D H : ℕ) (hD : 1 ≤ D)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : Nat.floor ((D : ℝ) ^ (11 / 10 : ℝ)) ≤ H) :
    selected.image (fun i => p i ^ 6) ⊆ rowNormDisk H := by
  classical
  intro u hu
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  rw [mem_rowNormDisk]
  have hpNorm : Ideal.absNorm (Ideal.span {p i}) ≠ 0 :=
    (Ideal.absNorm_eq_zero_iff).not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (hp i hi))
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hupper : (Ideal.absNorm (Ideal.span {p i ^ 6}) : ℝ) ≤
      (D : ℝ) ^ (11 / 10 : ℝ) := by
    calc
      (Ideal.absNorm (Ideal.span {p i ^ 6}) : ℝ) =
          (Ideal.absNorm (Ideal.span {p i}) : ℝ) ^ 6 := by
            exact_mod_cast ActualEisensteinCubic.principal_absNorm_pow (p i) 6
      _ ≤ ((D : ℝ) ^ (11 / 60 : ℝ)) ^ 6 := by
        gcongr
        exact hnormupper i hi
      _ = (D : ℝ) ^ (11 / 10 : ℝ) := by
        rw [← Real.rpow_mul_natCast hDpos.le (11 / 60 : ℝ) 6]
        congr 1
        norm_num
  constructor
  · rw [ActualEisensteinCubic.principal_absNorm_pow]
    exact pow_pos (Nat.pos_of_ne_zero hpNorm) 6
  · exact (Nat.le_floor hupper).trans hH

theorem baseChange_prime_extraction_from_MS
    {β : Type*} {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (F : Finset (Ideal O))
    (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (hW : ∀ n, ‖W n‖ ≤ 1)
    (selected : Finset β) (p : β → O)
    (D H : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hFnorm : ∀ I ∈ F, Ideal.absNorm I ≤ D)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : Nat.floor ((D : ℝ) ^ (11 / 10 : ℝ)) ≤ H)
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤ (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rowNormDisk H,
        ‖idealRowSum F hFpos hFgood χ W u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ I ∈ F, baseChangeWeight χ I * W (Ideal.absNorm I)‖ ≤
      384 * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  classical
  let : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  let P : primePool F → Ideal O := fun i => i.1
  let support : O → Finset (primePool F) :=
    fun x => idealSupport F (Ideal.span {x})
  let columns : Finset O := F.image idealGenerator
  let weight : O → ℂ := columnWeight χ W
  have hsupport : ∀ x ∈ columns, ∀ i ∈ support x, x ∈ P i := by
    intro x hx i hi
    obtain ⟨I, hIF, rfl⟩ := Finset.mem_image.mp hx
    dsimp [support, P] at hi ⊢
    rw [span_idealGenerator I] at hi
    exact idealGenerator_mem_prime_of_support F hFpos I hIF i hi
  have hcolnorm : ∀ x ∈ columns,
      Ideal.absNorm (Ideal.span {x}) ≤ D := by
    intro x hx
    obtain ⟨I, hIF, rfl⟩ := Finset.mem_image.mp hx
    rw [span_idealGenerator I]
    exact hFnorm I hIF
  have hweight : ∀ x ∈ columns, ‖weight x‖ ≤ 1 := by
    intro x hx
    exact columnWeight_norm_le_one χ W hW x
  have hmean' :
      (∑ u ∈ rowNormDisk H,
        ‖∑ x ∈ columns,
          weight x * finiteSquarefreeRow P (primePool_good F hFgood)
            (support x) u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε) := by
    calc
      _ = ∑ u ∈ rowNormDisk H,
          ‖idealRowSum F hFpos hFgood χ W u‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro u hu
            change ‖elementRow F hFpos hFgood χ W u‖ ^ 2 =
              ‖idealRowSum F hFpos hFgood χ W u‖ ^ 2
            rw [elementRow_eq_idealRowSum]
      _ ≤ _ := hmean
  have hrows : selected.image (fun i => p i ^ 6) ⊆ rowNormDisk H :=
    sixth_power_rows_in_rowNormDisk selected p D H hD hp hnormupper hH
  have hbound := finite_actual_prime_extraction_dyadic
    P (primePool_good F hFgood) columns support weight selected p
    (rowNormDisk H) D ε hD hε hp hprime hinj hrows
    hsupport hcolnorm hweight hnormlower hcount hmean'
  have hsum :
      (∑ x ∈ columns, weight x) =
        ∑ I ∈ F, baseChangeWeight χ I * W (Ideal.absNorm I) := by
    change (∑ x ∈ F.image idealGenerator, columnWeight χ W x) = _
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro I hIF
      exact columnWeight_idealGenerator χ W I
    · intro I hIF J hJF h
      exact idealGenerator_injective h
  rwa [hsum] at hbound

end

open ShortDraftHeckeBridge FiniteSFactor

noncomputable def outsideIdealsUpTo (S : Finset (Ideal O)) (D : ℕ) :
    Finset (Ideal O) := by
  classical
  exact (idealsUpTo D).filter (fun I => ∀ P ∈ S, ¬ P ∣ I)

theorem mem_outsideIdealsUpTo {S : Finset (Ideal O)} {D : ℕ}
    {I : Ideal O} :
    I ∈ outsideIdealsUpTo S D ↔
      1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D ∧
        (∀ P ∈ S, ¬ P ∣ I) := by
  classical
  simp [outsideIdealsUpTo, mem_idealsUpTo, and_assoc]

theorem outsideIdealsUpTo_ne_bot (S : Finset (Ideal O)) (D : ℕ)
    (I : Ideal O) (hI : I ∈ outsideIdealsUpTo S D) : I ≠ ⊥ := by
  have hn := (mem_outsideIdealsUpTo.mp hI).1
  intro h
  subst I
  simp at hn

theorem outsideIdealsUpTo_norm_le (S : Finset (Ideal O)) (D : ℕ)
    (I : Ideal O) (hI : I ∈ outsideIdealsUpTo S D) :
    Ideal.absNorm I ≤ D :=
  (mem_outsideIdealsUpTo.mp hI).2.1

theorem goodLambda_prime : Prime goodLambda := by
  let : IsCyclotomicExtension {3} ℚ K :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

theorem goodLambdaIdeal_maximal :
    (Ideal.span {goodLambda} : Ideal O).IsMaximal := by
  have hp : (Ideal.span {goodLambda} : Ideal O).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime goodLambda_prime
  have hne : (Ideal.span {goodLambda} : Ideal O) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr goodLambda_prime.ne_zero
  exact hp.isMaximal hne

theorem badPrime_cover_of_lambdaIdeal_mem
    (S : Finset (Ideal O))
    (hS : (Ideal.span {goodLambda} : Ideal O) ∈ S) :
    ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S := by
  intro P hP hmem
  have hle : (Ideal.span {goodLambda} : Ideal O) ≤ P :=
    (Ideal.span_singleton_le_iff_mem P).mpr hmem
  have heq : (Ideal.span {goodLambda} : Ideal O) = P :=
    goodLambdaIdeal_maximal.eq_of_le hP.ne_top hle
  rwa [heq] at hS

theorem outsideIdealsUpTo_good
    (S : Finset (Ideal O)) (D : ℕ)
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (I : Ideal O) (hI : I ∈ outsideIdealsUpTo S D)
    (Q : Ideal O) (hQ : Q ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    goodLambda ∉ Q := by
  intro hmemLam
  have hne : I ≠ ⊥ := outsideIdealsUpTo_ne_bot S D I hI
  have hp : Prime Q := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
  have hmax : Q.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hQS : Q ∈ S := hSbad Q hmax hmemLam
  have hdiv : Q ∣ I := (Ideal.dvd_iff_le).mpr
    ((Ideal.mem_normalizedFactors_iff hne).mp hQ).2
  exact (mem_outsideIdealsUpTo.mp hI).2.2 Q hQS hdiv

theorem idealsUpTo_eq_biUnion_fibers (D : ℕ) :
    idealsUpTo D =
      (Finset.Icc 1 D).biUnion FiniteSFactor.fiber := by
  rfl

private theorem normFibers_pairwiseDisjoint (D : ℕ) :
    ((Finset.Icc 1 D : Finset ℕ) : Set ℕ).PairwiseDisjoint
      FiniteSFactor.fiber := by
  intro n hn m hm hnm
  apply Finset.disjoint_left.mpr
  intro I hIn hIm
  exact hnm ((FiniteSFactor.mem_fiber.mp hIn).symm.trans
    (FiniteSFactor.mem_fiber.mp hIm))

theorem outsideIdealSum_eq_outsideCoeff_sum
    (S : Finset (Ideal O)) (D : ℕ)
    (w : Ideal O → ℂ) (W : ℕ → ℂ) :
    (∑ I ∈ outsideIdealsUpTo S D,
      w I * W (Ideal.absNorm I)) =
      ∑ n ∈ Finset.Icc 1 D,
        FiniteSFactor.outsideCoeff S w n * W n := by
  classical
  have hsets : outsideIdealsUpTo S D =
      (Finset.Icc 1 D).biUnion (fun n =>
        (FiniteSFactor.fiber n).filter (fun I => ∀ P ∈ S, ¬P ∣ I)) := by
    ext I
    simp [outsideIdealsUpTo, idealsUpTo_eq_biUnion_fibers,
      FiniteSFactor.mem_fiber, Finset.mem_biUnion]
  rw [hsets, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [FiniteSFactor.outsideCoeff, Finset.sum_mul, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro I hI
    rw [FiniteSFactor.mem_fiber.mp hI]
    by_cases hgood : ∀ P ∈ S, ¬P ∣ I <;>
      simp [FiniteSFactor.outsideWeight, hgood]
  · intro n hn m hm hnm
    exact Finset.disjoint_filter_filter
      (normFibers_pairwiseDisjoint D hn hm hnm)

theorem outsideCoeff_prime_extraction_from_MS
    {β : Type*} {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (hW : ∀ n, ‖W n‖ ≤ 1)
    (selected : Finset β) (p : β → O)
    (D H : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : Nat.floor ((D : ℝ) ^ (11 / 10 : ℝ)) ≤ H)
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤ (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rowNormDisk H,
        ‖idealRowSum (outsideIdealsUpTo S D)
            (outsideIdealsUpTo_ne_bot S D)
            (outsideIdealsUpTo_good S D hSbad)
            χ W u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ n ∈ Finset.Icc 1 D,
        FiniteSFactor.outsideCoeff S (baseChangeWeight χ) n * W n‖ ≤
      384 * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  let F := outsideIdealsUpTo S D
  have hbound := baseChange_prime_extraction_from_MS χ W F
    (outsideIdealsUpTo_ne_bot S D)
    (outsideIdealsUpTo_good S D hSbad)
    hW selected p D H ε hD hε
    (outsideIdealsUpTo_norm_le S D)
    hp hprime hinj hnormlower hnormupper hH hcount hmean
  simpa only [F, outsideIdealSum_eq_outsideCoeff_sum] using hbound

open ShortDraftHeckeBridge FiniteSFactor Filter

theorem eventually_absorb_MS_and_count_constants
    (Cmean Ccount eta : ℝ) (hcount : 0 < Ccount) (heta : 0 < eta) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      Cmean ≤ (D : ℝ) ^ eta ∧ 1 ≤ Ccount * (D : ℝ) ^ eta := by
  have hpow : Tendsto (fun D : ℕ => (D : ℝ) ^ eta) atTop atTop :=
    (tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp
    (hpow.eventually_ge_atTop (max Cmean Ccount⁻¹))
  refine ⟨D₀, fun D hD => ?_⟩
  have hlarge := hD₀ D hD
  constructor
  · exact (le_max_left _ _).trans hlarge
  · have hinv : Ccount⁻¹ ≤ (D : ℝ) ^ eta :=
      (le_max_right _ _).trans hlarge
    have hmul := mul_le_mul_of_nonneg_left hinv hcount.le
    simpa [hcount.ne'] using hmul

theorem outsideCoeff_prime_extraction_with_constants
    {β : Type*} {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (hW : ∀ n, ‖W n‖ ≤ 1)
    (selected : Finset β) (p : β → O)
    (D H : ℕ) (ε : ℝ) (eta : ℝ) (Cmean Ccount : ℝ)
    (hD : 1 ≤ D) (hε : 0 ≤ ε) (heta : 0 ≤ eta)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : Nat.floor ((D : ℝ) ^ (11 / 10 : ℝ)) ≤ H)
    (hcount : Ccount * (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤
      (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rowNormDisk H,
        ‖idealRowSum (outsideIdealsUpTo S D)
            (outsideIdealsUpTo_ne_bot S D)
            (outsideIdealsUpTo_good S D hSbad)
            χ W u‖ ^ 2) ≤
        Cmean * (D : ℝ) ^ ((21 / 10 : ℝ) + ε))
    (hmeanAbsorb : Cmean ≤ (D : ℝ) ^ eta)
    (hcountAbsorb : 1 ≤ Ccount * (D : ℝ) ^ eta) :
    ‖∑ n ∈ Finset.Icc 1 D,
        FiniteSFactor.outsideCoeff S (baseChangeWeight χ) n * W n‖ ≤
      384 * (D : ℝ) ^ ((23 / 24 : ℝ) + (ε + eta)) := by
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hcount' :
      (D : ℝ) ^ ((11 / 60 : ℝ) - (ε + eta)) ≤
        (selected.card : ℝ) := by
    calc
      (D : ℝ) ^ ((11 / 60 : ℝ) - (ε + eta)) =
          1 * (D : ℝ) ^ ((11 / 60 : ℝ) - (ε + eta)) := by ring
      _ ≤ (Ccount * (D : ℝ) ^ eta) *
          (D : ℝ) ^ ((11 / 60 : ℝ) - (ε + eta)) :=
            mul_le_mul_of_nonneg_right hcountAbsorb
              (Real.rpow_nonneg hDpos.le _)
      _ = Ccount * (D : ℝ) ^ ((11 / 60 : ℝ) - ε) := by
            rw [mul_assoc, ← Real.rpow_add hDpos]
            congr 1
            ring_nf
      _ ≤ (selected.card : ℝ) := hcount
  have hmean' :
      (∑ u ∈ rowNormDisk H,
        ‖idealRowSum (outsideIdealsUpTo S D)
            (outsideIdealsUpTo_ne_bot S D)
            (outsideIdealsUpTo_good S D hSbad)
            χ W u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + (ε + eta)) := by
    calc
      _ ≤ Cmean * (D : ℝ) ^ ((21 / 10 : ℝ) + ε) := hmean
      _ ≤ (D : ℝ) ^ eta * (D : ℝ) ^ ((21 / 10 : ℝ) + ε) :=
          mul_le_mul_of_nonneg_right hmeanAbsorb
            (Real.rpow_nonneg hDpos.le _)
      _ = (D : ℝ) ^ ((21 / 10 : ℝ) + (ε + eta)) := by
          rw [← Real.rpow_add hDpos]
          congr 1
          ring
  exact outsideCoeff_prime_extraction_from_MS χ W S hSbad hW selected p
    D H (ε + eta) hD (add_nonneg hε heta) hp hprime hinj
    hnormlower hnormupper hH hcount' hmean'

end ConcretePrimeRowBridge

end

end OAI

end



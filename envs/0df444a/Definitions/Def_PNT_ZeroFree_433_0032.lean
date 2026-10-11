-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0032
-- name    : PNT_ZeroFree_433_0032
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T13:55:02.387978+00:00
-- url     : https://prove2.me/theorems/409895b7-e3bd-4acb-b727-313ac9dc416e
-- title:
--   Zero-free region foundations: Hecke.FiniteEulerFactors [0032]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Hecke.FiniteEulerFactors
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/FiniteEulerFactors.lean#L48-L653

import Definitions.Def_PNT_ZeroFree_433_0030
import Definitions.Def_PNT_ZeroFree_433_0031

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Hecke/FiniteEulerFactors.lean#L48-L653
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Hecke.FiniteEulerFactors
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
namespace FiniteSFactor

private theorem fiber_card_natCard (n : ℕ) :
    (fiber n).card = Nat.card {I : Ideal O // Ideal.absNorm I = n} := by
  change (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset.card =
    Set.ncard {I : Ideal O | Ideal.absNorm I = n}
  exact (Set.ncard_eq_toFinset_card _ _).symm

private theorem fiber_card_le_count (n : ℕ) :
    (fiber n).card ≤ Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} := by
  let f : {I : Ideal O // Ideal.absNorm I = n} →
      {I : Ideal O // Ideal.absNorm I ≤ n} :=
    fun I => ⟨I.1, I.2.le⟩
  have hinj : Function.Injective f := by
    intro I J h
    have hval : I.1 = J.1 :=
      congrArg (fun x : {I : Ideal O // Ideal.absNorm I ≤ n} => x.1) h
    exact Subtype.ext hval
  have hfin : Finite {I : Ideal O // Ideal.absNorm I ≤ n} :=
    Ideal.finite_setOfPred_absNorm_le n
  simpa only [fiber_card_natCard] using Nat.card_le_card_of_injective f hinj

private theorem count_isBigO :
    (fun n : ℕ =>
      (Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  have hlim :=
    (NumberField.Ideal.tendsto_norm_le_div_atTop (CyclotomicField 3 ℚ)).comp
      tendsto_natCast_atTop_atTop
  have hlim' : Filter.Tendsto
      (fun n : ℕ =>
        (Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} : ℝ) / (n : ℝ))
      atTop (nhds ((2 ^ NumberField.InfinitePlace.nrRealPlaces (CyclotomicField 3 ℚ) *
        (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces (CyclotomicField 3 ℚ) *
        NumberField.Units.regulator (CyclotomicField 3 ℚ) *
        (NumberField.classNumber (CyclotomicField 3 ℚ) : ℝ)) /
        ((NumberField.Units.torsionOrder (CyclotomicField 3 ℚ) : ℝ) *
          Real.sqrt |(NumberField.discr (CyclotomicField 3 ℚ) : ℝ)|))) := by
    simpa [Function.comp_def] using hlim
  have hzero : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) = 0 →
        (Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} : ℝ) = 0 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn hz
    have hn0 : n = 0 := by exact_mod_cast hz
    exact (Nat.ne_of_gt hn hn0).elim
  exact Asymptotics.isBigO_of_div_tendsto_nhds hzero _ hlim'

private theorem fiber_card_eventually_le_linear :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ((fiber n).card : ℝ) ≤ C * n := by
  obtain ⟨C, hC⟩ := count_isBigO.bound
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n hn
  calc
    ((fiber n).card : ℝ) ≤
        (Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} : ℝ) := by
          exact_mod_cast fiber_card_le_count n
    _ = ‖(Nat.card {I : Ideal O // Ideal.absNorm I ≤ n} : ℝ)‖ := by simp
    _ ≤ C * ‖(n : ℝ)‖ := hn
    _ = C * n := by simp

private theorem outsideCoeff_norm_le_card (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (hw : ∀ I, ‖w I‖ ≤ 1) (n : ℕ) :
    ‖outsideCoeff S w n‖ ≤ ((fiber n).card : ℝ) := by
  classical
  have hweight (I : Ideal O) : ‖outsideWeight S w I‖ ≤ 1 := by
    by_cases hgood : ∀ P ∈ S, ¬P ∣ I
    · change ‖if ∀ P ∈ S, ¬P ∣ I then w I else 0‖ ≤ 1
      rw [if_pos hgood]
      exact hw I
    · change ‖if ∀ P ∈ S, ¬P ∣ I then w I else 0‖ ≤ 1
      rw [if_neg hgood]
      simp
  unfold outsideCoeff
  calc
    ‖∑ I ∈ fiber n, outsideWeight S w I‖ ≤
        ∑ I ∈ fiber n, ‖outsideWeight S w I‖ := norm_sum_le _ _
    _ ≤ ∑ _I ∈ fiber n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro I hI
      exact hweight I
    _ = ((fiber n).card : ℝ) := by simp

private theorem baseChangeWeight_norm_le_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    ‖ShortDraftHeckeBridge.baseChangeWeight χ I‖ ≤ 1 := by
  have hμ : ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ ≤ 1 := by
    by_cases hsq : Squarefree I
    · simp [hsq.moebius_eq]
    · simp [UniqueFactorizationMonoid.moebius_of_not_squarefree hsq]
  have hχ : ‖χ (Ideal.absNorm I)‖ ≤ 1 := χ.norm_le_one _
  rw [ShortDraftHeckeBridge.baseChangeWeight, norm_mul]
  calc
    ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ * ‖χ (Ideal.absNorm I)‖ ≤
        1 * ‖χ (Ideal.absNorm I)‖ :=
      mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
    _ ≤ 1 := by simpa using hχ

private theorem outsideCoeff_baseChange_isBigO_linear {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O)) :
    (fun n : ℕ => outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n)
      =O[atTop] (fun n : ℕ => (n : ℝ)) := by
  obtain ⟨C, hC⟩ := fiber_card_eventually_le_linear
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC] with n hn
  calc
    ‖outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n‖ ≤
        ((fiber n).card : ℝ) := outsideCoeff_norm_le_card S
          (ShortDraftHeckeBridge.baseChangeWeight χ)
          (baseChangeWeight_norm_le_one χ) n
    _ ≤ C * (n : ℝ) := hn
    _ = C * ‖(n : ℝ)‖ := by simp

theorem outsideCoeff_LSeriesSummable_baseChange {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O))
    (s : ℂ) (hs : 2 < s.re) :
    LSeriesSummable (outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)) s := by
  have hO :
      (fun n : ℕ => outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n)
        =O[atTop] (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) - 1)) := by
    simpa only [show ((2 : ℝ) - 1) = 1 by norm_num, Real.rpow_one] using
      outsideCoeff_baseChange_isBigO_linear χ S
  exact LSeriesSummable_of_isBigO_rpow hs hO

theorem outsideCoeff_exp_summable_baseChange {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O))
    (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => outsideCoeff S
      (ShortDraftHeckeBridge.baseChangeWeight χ) n * Real.exp (-(n : ℝ) * t)) := by
  obtain ⟨C, hC⟩ := fiber_card_eventually_le_linear
  have hexp : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ) * t)) := by
    convert! Real.summable_pow_mul_exp_neg_nat_mul 1 ht using 1
    ext n
    simp only [pow_one]
    congr 1
    ring_nf
  apply (hexp.mul_left C).of_norm_bounded_eventually_nat
  filter_upwards [hC] with n hn
  have hcoeff := outsideCoeff_norm_le_card S
    (ShortDraftHeckeBridge.baseChangeWeight χ)
    (baseChangeWeight_norm_le_one χ) n
  have hlin : ‖outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n‖ ≤
      C * (n : ℝ) := hcoeff.trans hn
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-(n : ℝ) * t)).le)

theorem outsideExpSum_restore_baseChange {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPnot : P ∉ S)
    (t : ℝ) (ht : 0 < t) :
    outsideExpSum S (ShortDraftHeckeBridge.baseChangeWeight χ) t =
      outsideExpSum (insert P S) (ShortDraftHeckeBridge.baseChangeWeight χ) t +
        ShortDraftHeckeBridge.baseChangeWeight χ P *
          outsideExpSum (insert P S) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm P : ℝ) * t) := by
  have hN : (0 : ℝ) < (Ideal.absNorm P : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.1)
  exact outsideExpSum_restore_insert_prime S hS P hP hPnot
    (ShortDraftHeckeBridge.baseChangeWeight χ)
    (ShortDraftHeckeBridge.baseChangeWeight_zero_of_not_squarefree χ)
    (ShortDraftHeckeBridge.baseChangeWeight_mul_of_isRelPrime χ)
    t
    (outsideCoeff_exp_summable_baseChange χ (insert P S) t ht)
    (outsideCoeff_exp_summable_baseChange χ (insert P S)
      ((Ideal.absNorm P : ℝ) * t) (mul_pos hN ht))

theorem outsideExpSum_empty_eq_normFiberExpSum {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    outsideExpSum ∅ (ShortDraftHeckeBridge.baseChangeWeight χ) t =
      ShortDraftHeckeBridge.normFiberExpSum
        (ShortDraftHeckeBridge.baseChangeWeight χ) t := by
  unfold outsideExpSum ShortDraftHeckeBridge.normFiberExpSum
  congr 1

theorem normFiberExpSum_restore_two_primes {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (P Q : Ideal O) (hP : Prime P) (hQ : Prime Q) (hPQ : P ≠ Q)
    (t : ℝ) (ht : 0 < t) :
    ShortDraftHeckeBridge.normFiberExpSum
      (ShortDraftHeckeBridge.baseChangeWeight χ) t =
        outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ) t +
        ShortDraftHeckeBridge.baseChangeWeight χ Q *
          outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm Q : ℝ) * t) +
        ShortDraftHeckeBridge.baseChangeWeight χ P *
          outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm P : ℝ) * t) +
        ShortDraftHeckeBridge.baseChangeWeight χ P *
          ShortDraftHeckeBridge.baseChangeWeight χ Q *
          outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm Q : ℝ) * ((Ideal.absNorm P : ℝ) * t)) := by
  have hPnot : P ∉ (∅ : Finset (Ideal O)) := by simp
  have hQnot : Q ∉ ({P} : Finset (Ideal O)) := by simpa using hPQ.symm
  have hSP : ∀ R ∈ ({P} : Finset (Ideal O)), Prime R := by
    intro R hR
    simp only [Finset.mem_singleton] at hR
    subst R
    exact hP
  have hNP : (0 : ℝ) < (Ideal.absNorm P : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.1)
  have h0 := outsideExpSum_restore_baseChange χ ∅ (by simp) P hP hPnot t ht
  have h1 := outsideExpSum_restore_baseChange χ {P} hSP Q hQ hQnot t ht
  have h2 := outsideExpSum_restore_baseChange χ {P} hSP Q hQ hQnot
    ((Ideal.absNorm P : ℝ) * t) (mul_pos hNP ht)
  rw [outsideExpSum_empty_eq_normFiberExpSum] at h0
  simp only [Finset.insert_empty] at h0
  rw [h1, h2] at h0
  calc
    ShortDraftHeckeBridge.normFiberExpSum
        (ShortDraftHeckeBridge.baseChangeWeight χ) t =
      outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ) t +
      ShortDraftHeckeBridge.baseChangeWeight χ Q *
        outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
          ((Ideal.absNorm Q : ℝ) * t) +
      ShortDraftHeckeBridge.baseChangeWeight χ P *
        (outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
          ((Ideal.absNorm P : ℝ) * t) +
        ShortDraftHeckeBridge.baseChangeWeight χ Q *
          outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm Q : ℝ) * ((Ideal.absNorm P : ℝ) * t))) := h0
    _ = _ := by ring

private noncomputable def dirichletKernel (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else (n : ℂ) ^ (-s)

private theorem term_eq_mul_kernel (a : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term a s n = a n * dirichletKernel s n := by
  by_cases hn : n = 0
  · subst n
    simp [LSeries.term, dirichletKernel]
  · simp [LSeries.term, dirichletKernel, hn, div_eq_mul_inv, Complex.cpow_neg]

private theorem kernel_shift {N : ℕ} (hN : 0 < N) (s : ℂ) (m : ℕ) :
    dirichletKernel s (N * m) =
      (N : ℂ) ^ (-s) * dirichletKernel s m := by
  by_cases hm : m = 0
  · subst m
    simp [dirichletKernel]
  · have hNm : N * m ≠ 0 := mul_ne_zero hN.ne' hm
    simp only [dirichletKernel, if_neg hNm, if_neg hm]
    simpa only [Nat.cast_mul] using Complex.natCast_mul_natCast_cpow N m (-s)

private theorem tsum_mul_kernel_eq_LSeries (a : ℕ → ℂ) (s : ℂ) :
    (∑' n : ℕ, a n * dirichletKernel s n) = LSeries a s := by
  unfold LSeries
  apply tsum_congr
  intro n
  exact (term_eq_mul_kernel a s n).symm

theorem outsideLSeries_restore_baseChange {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPnot : P ∉ S)
    (s : ℂ) (hs : 2 < s.re) :
    LSeries (outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
      (1 + ShortDraftHeckeBridge.baseChangeWeight χ P *
        (Ideal.absNorm P : ℂ) ^ (-s)) *
        LSeries (outsideCoeff (insert P S)
          (ShortDraftHeckeBridge.baseChangeWeight χ)) s := by
  let N : ℕ := Ideal.absNorm P
  let a : ℕ → ℂ := outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)
  let b : ℕ → ℂ := outsideCoeff (insert P S) (ShortDraftHeckeBridge.baseChangeWeight χ)
  let c : ℂ := ShortDraftHeckeBridge.baseChangeWeight χ P
  have hN : 0 < N :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.1)
  have hcoeff (n : ℕ) :
      a n = b n + if N ∣ n then c * b (n / N) else 0 :=
    restore_insert_prime S hS P hP hPnot
      (ShortDraftHeckeBridge.baseChangeWeight χ)
      (ShortDraftHeckeBridge.baseChangeWeight_zero_of_not_squarefree χ)
      (ShortDraftHeckeBridge.baseChangeWeight_mul_of_isRelPrime χ) n
  have hbsum : LSeriesSummable b s :=
    outsideCoeff_LSeriesSummable_baseChange χ (insert P S) s hs
  change Summable (LSeries.term b s) at hbsum
  have hb : Summable (fun n : ℕ => b n * dirichletKernel s n) := by
    simpa only [← term_eq_mul_kernel b s] using hbsum
  have hshiftPoint (m : ℕ) :
      b m * dirichletKernel s (N * m) =
        (N : ℂ) ^ (-s) * LSeries.term b s m := by
    rw [kernel_shift hN s m, term_eq_mul_kernel]
    ring
  have hshift : Summable (fun m : ℕ => b m * dirichletKernel s (N * m)) := by
    simpa only [hshiftPoint] using hbsum.mul_left ((N : ℂ) ^ (-s))
  have hgeneric := FiniteEulerRestoration.tsum_restore_one_prime hN c a b
    (dirichletKernel s) hcoeff hb hshift
  rw [tsum_mul_kernel_eq_LSeries a s, tsum_mul_kernel_eq_LSeries b s] at hgeneric
  have hshiftSum :
      (∑' m : ℕ, b m * dirichletKernel s (N * m)) =
        (N : ℂ) ^ (-s) * LSeries b s := by
    calc
      (∑' m : ℕ, b m * dirichletKernel s (N * m)) =
          ∑' m : ℕ, (N : ℂ) ^ (-s) * LSeries.term b s m := by
            apply tsum_congr
            exact hshiftPoint
      _ = (N : ℂ) ^ (-s) * LSeries b s := by
            rw [tsum_mul_left]
            rfl
  rw [hshiftSum] at hgeneric
  change LSeries a s = (1 + c * (N : ℂ) ^ (-s)) * LSeries b s
  calc
    LSeries a s = LSeries b s + c * ((N : ℂ) ^ (-s) * LSeries b s) := hgeneric
    _ = (1 + c * (N : ℂ) ^ (-s)) * LSeries b s := by ring

theorem outsideLSeries_finiteEuler_baseChange {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P)
    (s : ℂ) (hs : 2 < s.re) :
    LSeries (outsideCoeff ∅ (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
      (∏ P ∈ S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ P *
        (Ideal.absNorm P : ℂ) ^ (-s))) *
      LSeries (outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)) s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert P S hPnot ih =>
      have hSP : ∀ Q ∈ S, Prime Q := by
        intro Q hQ
        exact hS Q (Finset.mem_insert_of_mem hQ)
      have hPP : Prime P := hS P (Finset.mem_insert_self P S)
      have hrest := outsideLSeries_restore_baseChange χ S hSP P hPP hPnot s hs
      calc
        LSeries (outsideCoeff ∅ (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
            (∏ Q ∈ S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ Q *
              (Ideal.absNorm Q : ℂ) ^ (-s))) *
            LSeries (outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)) s :=
          ih hSP
        _ = (∏ Q ∈ S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ Q *
              (Ideal.absNorm Q : ℂ) ^ (-s))) *
            ((1 + ShortDraftHeckeBridge.baseChangeWeight χ P *
              (Ideal.absNorm P : ℂ) ^ (-s)) *
              LSeries (outsideCoeff (insert P S)
                (ShortDraftHeckeBridge.baseChangeWeight χ)) s) := by rw [hrest]
        _ = (∏ Q ∈ insert P S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ Q *
              (Ideal.absNorm Q : ℂ) ^ (-s))) *
            LSeries (outsideCoeff (insert P S)
              (ShortDraftHeckeBridge.baseChangeWeight χ)) s := by
          rw [Finset.prod_insert hPnot]
          ring

theorem outsideCoeff_empty_eq_normFiberCoeff (w : Ideal O → ℂ) (n : ℕ) :
    outsideCoeff ∅ w n = ShortDraftHeckeBridge.normFiberCoeff w n := by
  simp [outsideCoeff, outsideWeight, fiber, ShortDraftHeckeBridge.normFiberCoeff]

theorem normFiberLSeries_finiteEuler_baseChange {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (s : ℂ) (hs : 2 < s.re) :
    LSeries (ShortDraftHeckeBridge.normFiberCoeff
      (ShortDraftHeckeBridge.baseChangeWeight χ)) s =
      (∏ P ∈ S, (1 - χ (Ideal.absNorm P) *
        (Ideal.absNorm P : ℂ) ^ (-s))) *
      LSeries (outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ)) s := by
  have h := outsideLSeries_finiteEuler_baseChange χ S hS s hs
  have hfun : outsideCoeff ∅ (ShortDraftHeckeBridge.baseChangeWeight χ) =
      ShortDraftHeckeBridge.normFiberCoeff
        (ShortDraftHeckeBridge.baseChangeWeight χ) := by
    funext n
    exact outsideCoeff_empty_eq_normFiberCoeff _ n
  rw [hfun] at h
  have hprod :
      (∏ P ∈ S, (1 + ShortDraftHeckeBridge.baseChangeWeight χ P *
        (Ideal.absNorm P : ℂ) ^ (-s))) =
      (∏ P ∈ S, (1 - χ (Ideal.absNorm P) *
        (Ideal.absNorm P : ℂ) ^ (-s))) := by
    apply Finset.prod_congr rfl
    intro P hPS
    rw [ShortDraftHeckeBridge.baseChangeWeight_prime χ P (hS P hPS)]
    ring
  rw [hprod] at h
  exact h

end FiniteSFactor

open Filter

namespace CompactScaleBridge

open ConcretePrimeRowBridge ShortDraftHeckeBridge

abbrev O := ConcretePrimeRowBridge.O

theorem idealsUpTo_card_le (N : ℕ) :
    (idealsUpTo N).card ≤ 64 * (N + 1) := by
  classical
  have himage : (columnsUpTo N).card = (idealsUpTo N).card := by
    unfold columnsUpTo
    exact Finset.card_image_of_injective _ idealGenerator_injective
  rw [← himage]
  apply ShortDraftLatticeCount.actual_eisenstein_count
  intro x hx
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hx
  have hnorm : Ideal.absNorm I ≤ N := (mem_idealsUpTo.mp hI).2
  have hqNat : ShortDraftLatticeCount.qNat (idealGenerator I) ≤ N := by
    rw [ActualEisensteinCubic.qNat_eq_absNorm_span, span_idealGenerator]
    exact hnorm
  have hnonneg := ShortDraftLatticeCount.qO_nonneg (idealGenerator I)
  have hcast : ((ShortDraftLatticeCount.q
      (ActualEisensteinCoordinates.coords (idealGenerator I))).toNat : ℤ) =
      ShortDraftLatticeCount.q
        (ActualEisensteinCoordinates.coords (idealGenerator I)) :=
    Int.toNat_of_nonneg hnonneg
  change (ShortDraftLatticeCount.q
    (ActualEisensteinCoordinates.coords (idealGenerator I))).toNat ≤ N at hqNat
  have hqInt :
      ((ShortDraftLatticeCount.q
        (ActualEisensteinCoordinates.coords (idealGenerator I))).toNat : ℤ) ≤ N := by
    exact_mod_cast hqNat
  simpa only [hcast] using hqInt

theorem outsideIdealsUpTo_card_le (S : Finset (Ideal O)) (N : ℕ) :
    (outsideIdealsUpTo S N).card ≤ 64 * (N + 1) := by
  classical
  calc
    (outsideIdealsUpTo S N).card ≤ (idealsUpTo N).card := by
      apply Finset.card_le_card
      intro I hI
      exact (Finset.mem_filter.mp hI).1
    _ ≤ _ := idealsUpTo_card_le N

theorem integer_fixed_test_identity
    (S : Finset (Ideal O)) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℝ → ℂ) (m : ℕ) (hm : 0 < m) :
    (∑ I ∈ outsideIdealsUpTo S (2 * m),
      baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ))) =
    ∑ n ∈ Finset.Icc 1 (2 * m),
      FiniteSFactor.outsideCoeff S (baseChangeWeight χ) n *
        (fun y : ℝ => W (2 * y)) ((n : ℝ) / (2 * m : ℕ)) := by
  convert! outsideIdealSum_eq_outsideCoeff_sum S (2 * m)
    (baseChangeWeight χ) (fun n => W ((n : ℝ) / (m : ℝ))) using 1
  simp only
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  push_cast
  field_simp

theorem real_to_integer_compact_bound
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (W : ℝ → ℂ)
    (LipC D : ℝ) (m : ℕ)
    (hL : 0 ≤ LipC) (hLip : ∀ x y : ℝ, ‖W x - W y‖ ≤ LipC * |x - y|)
    (hD : 1 ≤ D) (hmLower : D ≤ (m : ℝ))
    (hmUpper : (m : ℝ) ≤ D + 1) :
    ‖(∑ I ∈ outsideIdealsUpTo S (2 * m),
        baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)) -
      (∑ I ∈ outsideIdealsUpTo S (2 * m),
        baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))‖ ≤
      640 * LipC := by
  classical
  let F := outsideIdealsUpTo S (2 * m)
  have hDpos : 0 < D := by linarith
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le hDpos hmLower
  have hcardNat : F.card ≤ 64 * (2 * m + 1) :=
    outsideIdealsUpTo_card_le S (2 * m)
  have hcard : (F.card : ℝ) ≤ 320 * D := by
    have hcardReal : (F.card : ℝ) ≤ 64 * (2 * (m : ℝ) + 1) := by
      exact_mod_cast hcardNat
    nlinarith
  have hpoint (I : Ideal O) (hIF : I ∈ F) :
      ‖baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D) -
        baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ))‖ ≤
      2 * LipC / D := by
    let n : ℝ := Ideal.absNorm I
    have hn0 : 0 ≤ n := by positivity
    have hn : n ≤ 2 * (m : ℝ) := by
      have hh : Ideal.absNorm I ≤ 2 * m :=
        (mem_outsideIdealsUpTo.mp hIF).2.1
      have hh' : (Ideal.absNorm I : ℝ) ≤ (2 * m : ℕ) := by
        exact_mod_cast hh
      simpa only [n, Nat.cast_mul, Nat.cast_ofNat] using hh'
    have hgap : 0 ≤ (m : ℝ) - D := sub_nonneg.mpr hmLower
    have hgap1 : (m : ℝ) - D ≤ 1 := by linarith
    have hnum : n * ((m : ℝ) - D) ≤ 2 * (m : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) hgap,
        mul_nonneg hn0 (sub_nonneg.mpr hgap1)]
    have hxy : n / (m : ℝ) ≤ n / D := by
      apply (div_le_div_iff₀ hmpos hDpos).2
      nlinarith [mul_nonneg hn0 hgap]
    have hdiff : n / D - n / (m : ℝ) ≤ 2 / D := by
      have haux : n * ((m : ℝ) - D) / (D * (m : ℝ)) ≤ 2 / D := by
        apply (div_le_div_iff₀ (mul_pos hDpos hmpos) hDpos).2
        nlinarith [mul_le_mul_of_nonneg_right hnum hDpos.le]
      have hfactor : n / D - n / (m : ℝ) =
          n * ((m : ℝ) - D) / (D * (m : ℝ)) := by
        field_simp
      rw [hfactor]
      exact haux
    have habs : |n / D - n / (m : ℝ)| ≤ 2 / D := by
      rwa [abs_of_nonneg (sub_nonneg.mpr hxy)]
    have hW := hLip (n / D) (n / (m : ℝ))
    have hwNorm := baseChangeWeight_norm_le_one χ I
    calc
      ‖baseChangeWeight χ I * W (n / D) -
          baseChangeWeight χ I * W (n / (m : ℝ))‖ =
          ‖baseChangeWeight χ I‖ *
            ‖W (n / D) - W (n / (m : ℝ))‖ := by
              rw [← mul_sub, norm_mul]
      _ ≤ 1 * (LipC * |n / D - n / (m : ℝ)|) :=
        mul_le_mul hwNorm hW (norm_nonneg _) (by positivity)
      _ ≤ 1 * (LipC * (2 / D)) := by
        gcongr
      _ = 2 * LipC / D := by ring
  calc
    ‖(∑ I ∈ F, baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)) -
      (∑ I ∈ F, baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))‖ =
        ‖∑ I ∈ F,
          (baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D) -
            baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))‖ := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ I ∈ F,
          ‖baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D) -
            baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ))‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _I ∈ F, (2 * LipC / D) := by
      apply Finset.sum_le_sum
      exact hpoint
    _ = (F.card : ℝ) * (2 * LipC / D) := by simp [mul_comm]
    _ ≤ 640 * LipC := by
      have hcoef : 0 ≤ 2 * LipC / D := by positivity
      calc
        (F.card : ℝ) * (2 * LipC / D) ≤
            (320 * D) * (2 * LipC / D) :=
          mul_le_mul_of_nonneg_right hcard hcoef
        _ = 640 * LipC := by
          field_simp
          ring

theorem smooth_supported_hasLipschitzConstant
    (W : ℝ → ℂ) (hSmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hSupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0) :
    ∃ LipC : ℝ, 0 ≤ LipC ∧
      ∀ x y : ℝ, ‖W x - W y‖ ≤ LipC * |x - y| := by
  have hCompact : HasCompactSupport W := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro x hx
    constructor
    · by_contra h
      have hxle : x ≤ 1 := le_of_not_ge h
      exact hx (hSupp x (Or.inl hxle))
    · by_contra h
      have hxge : 2 ≤ x := le_of_not_ge h
      exact hx (hSupp x (Or.inr hxge))
  obtain ⟨C, hC⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hCompact hSmooth (by simp)
  refine ⟨(C : ℝ), C.2, ?_⟩
  intro x y
  simpa only [dist_eq_norm, Real.norm_eq_abs] using hC.dist_le_mul x y

noncomputable def fixedTestWeight (W : ℝ → ℂ) (m n : ℕ) : ℂ :=
  W (2 * ((n : ℝ) / (2 * m : ℕ)))

theorem fixedTestWeight_eq (W : ℝ → ℂ) {m : ℕ} (hm : 0 < m) (n : ℕ) :
    fixedTestWeight W m n = W ((n : ℝ) / (m : ℝ)) := by
  unfold fixedTestWeight
  congr 1
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  push_cast
  field_simp

structure FixedTestPrimeMS
    {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (m : ℕ) (ε : ℝ) where
  H : ℕ
  selected : Finset O
  hp : ∀ p ∈ selected, p ≠ 0
  hprime : ∀ p ∈ selected, (Ideal.span {p} : Ideal O).IsMaximal
  hinj : Set.InjOn (fun p : O => (Ideal.span {p} : Ideal O)) (selected : Set O)
  hnormlower : ∀ p ∈ selected,
    ((2 * m : ℕ) : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ)
  hnormupper : ∀ p ∈ selected,
    (Ideal.absNorm (Ideal.span {p}) : ℝ) ≤
      ((2 * m : ℕ) : ℝ) ^ (11 / 60 : ℝ)
  hH : Nat.floor (((2 * m : ℕ) : ℝ) ^ (11 / 10 : ℝ)) ≤ H
  hcount : ((2 * m : ℕ) : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤
    (selected.card : ℝ)
  hmean :
    (∑ u ∈ rowNormDisk H,
      ‖idealRowSum (outsideIdealsUpTo S (2 * m))
          (outsideIdealsUpTo_ne_bot S (2 * m))
          (outsideIdealsUpTo_good S (2 * m) hSbad)
          χ (fixedTestWeight W m) u‖ ^ 2) ≤
      ((2 * m : ℕ) : ℝ) ^ ((21 / 10 : ℝ) + ε)

theorem FixedTestPrimeMS.bound
    {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (m : ℕ) (ε : ℝ)
    (h : FixedTestPrimeMS χ S hSbad W m ε)
    (hm : 0 < m) (hε : 0 ≤ ε) (hW : ∀ y : ℝ, ‖W y‖ ≤ 1) :
    ‖∑ I ∈ outsideIdealsUpTo S (2 * m),
      baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ))‖ ≤
      384 * ((2 * m : ℕ) : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  have hWeight : ∀ n : ℕ, ‖fixedTestWeight W m n‖ ≤ 1 := by
    intro n
    exact hW _
  have hD : 1 ≤ 2 * m := by omega
  have hbound := outsideCoeff_prime_extraction_from_MS χ
    (fixedTestWeight W m) S hSbad hWeight h.selected (fun p : O => p)
    (2 * m) h.H ε hD hε h.hp h.hprime h.hinj h.hnormlower
    h.hnormupper h.hH h.hcount h.hmean
  rw [← outsideIdealSum_eq_outsideCoeff_sum] at hbound
  simpa only [fixedTestWeight_eq W hm] using hbound

end CompactScaleBridge

end

end OAI

end



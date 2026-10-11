-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0083
-- name    : PNT_ZeroFree_433_0083
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:51:18.011659+00:00
-- url     : https://prove2.me/theorems/1ee78fb5-df87-45ad-aeff-fa8a012864f0
-- title:
--   Zero-free region foundations: QuadraticSieve.AnnularRecursion [0083]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.AnnularRecursion
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/AnnularRecursion.lean#L80-L634

import Definitions.Def_PNT_ZeroFree_433_0082

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/AnnularRecursion.lean#L80-L634
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.AnnularRecursion
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator
open IdealCoprimeSieveOperator DivisorBlockCauchy FiniteSieveRestriction

def weightedRayGramMatrix {m n : Type*} [Fintype m]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (rows : m → Ideal O) (cols : n → Ideal O)
    (v : m → ℝ) : Matrix n n ℂ :=
  fun j k => ∑ i, (v i : ℂ) *
    (if gcd (cols j) (cols k) = D ∧ columnRay (cols j) = c ∧ columnRay (cols k) = c then
      star (quadraticRow (cols j) (primaryGenerator (rows i))) *
        quadraticRow (cols k) (primaryGenerator (rows i)) else 0)

theorem weightedRayGcdBlock_eq_quadraticForm {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (rows : m → Ideal O) (cols : n → Ideal O)
    (v : m → ℝ) (a : n → ℂ) :
    weightedRayGcdBlock D c rows cols v a =
      ∑ j, ∑ k, star (a j) * weightedRayGramMatrix D c rows cols v j k * a k := by
  unfold weightedRayGcdBlock weightedGcdBlock
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [weightedRayGramMatrix, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  unfold gcdTerm sectorCoefficient
  by_cases hg : gcd (cols j) (cols k) = D <;>
    by_cases hj : columnRay (cols j) = c <;> by_cases hk : columnRay (cols k) = c <;>
      simp only [hg, hj, hk, ↓reduceIte, true_and, false_and, and_false,
        mul_zero, zero_mul, star_zero, star_mul] ; ring

theorem smoothRayGcdBlock_norm_le (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    ‖smoothRayGcdBlock M N K D c a‖ ≤
      ‖operator (weightedRayGramMatrix D c (fun I : highKernelRange (2 * M) K => I.val)
        (fun J : idealRange N => J.val) (fun I => smoothHighWeight M I.val))‖ * ∑ J, ‖a J‖ ^ 2 := by
  unfold smoothRayGcdBlock
  rw [weightedRayGcdBlock_eq_quadraticForm]
  exact quadratic_form_bound _ _

def smoothRayThirdNorm (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) : ℝ :=
  sSup (Set.range (fun a : idealRange N → ℂ =>
    ‖smoothRayGcdBlock M N K D c a‖ / (∑ J, ‖a J‖ ^ 2)))

def smoothThirdNorm (M N K : ℝ) (D : Ideal O) : ℝ :=
  ∑ c : EisensteinEPrimaryPhase.Coord, smoothRayThirdNorm M N K D c

theorem smoothRayThirdNorm_bddAbove (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    BddAbove (Set.range (fun a : idealRange N → ℂ =>
      ‖smoothRayGcdBlock M N K D c a‖ / (∑ J, ‖a J‖ ^ 2))) := by
  refine ⟨‖operator (weightedRayGramMatrix D c (fun I : highKernelRange (2 * M) K => I.val)
    (fun J : idealRange N => J.val) (fun I => smoothHighWeight M I.val))‖, ?_⟩
  rintro x ⟨a, rfl⟩
  dsimp only
  have he : 0 ≤ ∑ J, ‖a J‖ ^ 2 := by positivity
  rcases he.eq_or_lt with he | he
  · rw [← he, div_zero]
    exact norm_nonneg _
  · exact (div_le_iff₀ he).mpr (smoothRayGcdBlock_norm_le M N K D c a)

theorem smoothRayThirdNorm_nonneg (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    0 ≤ smoothRayThirdNorm M N K D c := by
  unfold smoothRayThirdNorm
  apply le_csSup (smoothRayThirdNorm_bddAbove M N K D c)
  refine ⟨(fun _ => 0), ?_⟩
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, div_zero]

theorem smoothThirdNorm_nonneg (M N K : ℝ) (D : Ideal O) : 0 ≤ smoothThirdNorm M N K D :=
  Finset.sum_nonneg (fun c _ => smoothRayThirdNorm_nonneg M N K D c)

theorem smoothRayThirdNorm_bound (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    ‖smoothRayGcdBlock M N K D c a‖ ≤ smoothRayThirdNorm M N K D c * ∑ J, ‖a J‖ ^ 2 := by
  have he : 0 ≤ ∑ J, ‖a J‖ ^ 2 := by positivity
  rcases he.eq_or_lt with he | he
  · have hb := smoothRayGcdBlock_norm_le M N K D c a
    simpa only [← he, mul_zero] using hb
  · exact (div_le_iff₀ he).mp (le_csSup (smoothRayThirdNorm_bddAbove M N K D c) (Set.mem_range_self a))

theorem highKernelNorm_le_smoothThirdNorm (M N K G : ℝ)
    (hM : 0 < M) (hN : 1 ≤ N) (hG : 0 < G) (ε : ℝ) (hε : 0 < ε) :
    highKernelNorm M N K ≤ 16 *
      ((∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          smoothThirdNorm M N K D) +
        highKernelNorm (2 * M) (N / G) K * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2) := by
  apply squared_norm_le_of_energy _ _
  · have hb := highKernelNorm_nonneg (2 * M) (N / G) K
    have hs := (supportConstant_pos ε hε).le
    have hd := (divisorConstant_pos ε hε).le
    have ht : 0 ≤ ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
        smoothThirdNorm M N K D := Finset.sum_nonneg (fun D _ => smoothThirdNorm_nonneg M N K D)
    positivity
  · intro a
    have h := highKernel_energy_smooth_gcd_reduction M N K G hM hN hG ε hε a
    apply h.trans
    have hsum : (∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖smoothRayGcdBlock M N K D c a‖) ≤
        (∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          smoothThirdNorm M N K D) * ∑ J, ‖a J‖ ^ 2 := by
      calc
        _ ≤ ∑ c : EisensteinEPrimaryPhase.Coord,
            ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
              smoothRayThirdNorm M N K D c * ∑ J, ‖a J‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro c _
          exact Finset.sum_le_sum (fun D _ => smoothRayThirdNorm_bound M N K D c a)
        _ = _ := by rw [Finset.sum_comm]; simp only [smoothThirdNorm, Finset.sum_mul]
    nlinarith

end

section
open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction
open QuadraticSquarefreeKernel

def rayPairValue (N : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) (I : Ideal O) : ℂ :=
  ∑ J : idealRange N, ∑ lengthScale : idealRange N,
    gcdTerm D (fun _ : Unit => I) (fun J : idealRange N => J.val)
      (sectorCoefficient (fun J : idealRange N => columnRay J.val) c a) () J lengthScale

theorem rayPairValue_eq (N : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) (I : Ideal O) :
    rayPairValue N D c a I = ∑ J : idealRange N, ∑ lengthScale : idealRange N,
      if gcd J.val lengthScale.val = D ∧ columnRay J.val = c ∧ columnRay lengthScale.val = c then
        star (quadraticRow J.val (primaryGenerator I) * a J) *
          (quadraticRow lengthScale.val (primaryGenerator I) * a lengthScale) else 0 := by
  simpa only [rayPairValue, rayGcdBlock, gcdBlock, Fintype.sum_unique, gcdTerm] using
    rayGcdBlock_eq D c (fun _ : Unit => I) (fun J : idealRange N => J.val) a

theorem smoothHighWeight_eq_zero (M : ℝ) (hM : 0 < M) (I : Ideal O)
    (hI : 2 * M ≤ (Ideal.absNorm I : ℝ)) : smoothHighWeight M I = 0 := by
  have ht : 2 ≤ (Ideal.absNorm I : ℝ) / M := (le_div_iff₀ hM).mpr (by linarith)
  have hnonneg : 0 ≤ (Ideal.absNorm I : ℝ) / M := div_nonneg (Nat.cast_nonneg _) hM.le
  by_contra hn
  have hm : (Ideal.absNorm I : ℝ) / M ∈ Function.support QuadraticInitialBound.sieveBump := hn
  rw [QuadraticInitialBound.sieveBump.support_eq] at hm
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hm
  change (Ideal.absNorm I : ℝ) / M < 2 at hm
  linarith

theorem smoothRayGcdBlock_eq_finite (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    smoothRayGcdBlock M N K D c a =
      ∑ I : highKernelRange (2 * M) K, (smoothHighWeight M I.val : ℂ) * rayPairValue N D c a I.val := by
  rfl

theorem smoothRayGcdBlock_eq_tsum (M N K : ℝ) (hM : 0 < M)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (a : idealRange N → ℂ) :
    smoothRayGcdBlock M N K D c a =
      ∑' I : Ideal O, if Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) then
        QuadraticInitialBound.sieveCutoff ((Ideal.absNorm I : ℝ) / M) * rayPairValue N D c a I else 0 := by
  rw [smoothRayGcdBlock_eq_finite,
    Finset.sum_coe_sort (highKernelRange (2 * M) K) (fun I => (smoothHighWeight M I : ℂ) * rayPairValue N D c a I)]
  symm
  rw [tsum_eq_sum (s := highKernelRange (2 * M) K) (fun I hI => ?_)]
  · apply Finset.sum_congr rfl
    intro I hI
    have hp : Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) := by
      have h := mem_highKernelRange.mp hI
      exact ⟨h.1, h.2.2⟩
    rw [if_pos hp, QuadraticInitialBound.sieveCutoff_apply]
    rfl
  · by_cases hp : Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ)
    · have hn : 2 * M < (Ideal.absNorm I : ℝ) := by
        by_contra hh
        exact hI (mem_highKernelRange.mpr ⟨hp.1, le_of_not_gt hh, hp.2⟩)
      rw [if_pos hp, QuadraticInitialBound.sieveCutoff_apply]
      change (smoothHighWeight M I : ℂ) * _ = 0
      rw [smoothHighWeight_eq_zero M hM I hn.le]
      simp
    · exact if_neg hp

end

open ActualEisensteinCubic CompletedGauss FiniteSieveOperator

def highKernelShellRange (M K : ℝ) : Finset (Ideal O) :=
  (highKernelRange M K).filter (fun I => M / 2 < (Ideal.absNorm I : ℝ))

theorem mem_highKernelShellRange {M K : ℝ} {I : Ideal O} :
    I ∈ highKernelShellRange M K ↔ I ∈ highKernelRange M K ∧ M / 2 < (Ideal.absNorm I : ℝ) :=
  Finset.mem_filter

def highKernelShellMatrix (M N K : ℝ) : Matrix (highKernelShellRange M K) (idealRange N) ℂ :=
  fun I J => quadraticRow J.val (primaryGenerator I.val)

def highKernelShellNorm (M N K : ℝ) : ℝ := ‖operator (highKernelShellMatrix M N K)‖ ^ 2

theorem highKernelShellNorm_nonneg (M N K : ℝ) : 0 ≤ highKernelShellNorm M N K := sq_nonneg _

theorem exists_dyadic_shell (n lengthScale : ℕ) (hn : 1 ≤ n) (hL : (n : ℝ) ≤ (2 : ℝ) ^ lengthScale) :
    ∃ j ∈ Finset.range (lengthScale + 1), (2 : ℝ) ^ j / 2 < n ∧ (n : ℝ) ≤ (2 : ℝ) ^ j := by
  have hex : ∃ j : ℕ, (n : ℝ) ≤ (2 : ℝ) ^ j := ⟨lengthScale, hL⟩
  let j := Nat.find hex
  have hj : (n : ℝ) ≤ (2 : ℝ) ^ j := Nat.find_spec hex
  have hjL : j ≤ lengthScale := Nat.find_min' hex hL
  refine ⟨j, Finset.mem_range.mpr (by omega), ?_, hj⟩
  have hjfind : j = Nat.find hex := rfl
  rcases j with _ | j
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    norm_num
    linarith
  · have hprev : ¬ (n : ℝ) ≤ (2 : ℝ) ^ j := Nat.find_min hex (by omega)
    have hp := lt_of_not_ge hprev
    simpa only [pow_succ, mul_div_cancel_right₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hp

theorem highKernel_dyadic_cover (M K : ℝ) (lengthScale : ℕ) (hML : M ≤ (2 : ℝ) ^ lengthScale)
    (I : Ideal O) (hI : I ∈ highKernelRange M K) :
    ∃ j ∈ Finset.range (lengthScale + 1), I ∈ highKernelShellRange ((2 : ℝ) ^ j) K := by
  obtain ⟨hs, hN, hk⟩ := mem_highKernelRange.mp hI
  have hn : 1 ≤ Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr
    (fun hz => hs.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  obtain ⟨j, hj, hlo, hhi⟩ := exists_dyadic_shell (Ideal.absNorm I) lengthScale hn (hN.trans hML)
  exact ⟨j, hj, mem_highKernelShellRange.mpr ⟨mem_highKernelRange.mpr ⟨hs, hhi, hk⟩, hlo⟩⟩

theorem highKernelNorm_le_dyadic_shells (M N K : ℝ) (lengthScale : ℕ) (hML : M ≤ (2 : ℝ) ^ lengthScale) :
    highKernelNorm M N K ≤ ∑ j ∈ Finset.range (lengthScale + 1), highKernelShellNorm ((2 : ℝ) ^ j) N K := by
  apply squared_norm_le_of_energy _ _ (Finset.sum_nonneg (fun j _ => highKernelShellNorm_nonneg _ _ _))
  intro a
  let E : Ideal O → ℝ := fun I => ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖ ^ 2
  have hE (I : Ideal O) : 0 ≤ E I := sq_nonneg _
  change (∑ I : highKernelRange M K, E I.val) ≤ _
  rw [Finset.sum_coe_sort (highKernelRange M K) E]
  calc
    _ ≤ ∑ I ∈ highKernelRange M K, ∑ j ∈ Finset.range (lengthScale + 1),
        if I ∈ highKernelShellRange ((2 : ℝ) ^ j) K then E I else 0 := by
      apply Finset.sum_le_sum
      intro I hI
      obtain ⟨j, hj, hIj⟩ := highKernel_dyadic_cover M K lengthScale hML I hI
      have h := Finset.single_le_sum (s := Finset.range (lengthScale + 1))
        (f := fun j => if I ∈ highKernelShellRange ((2 : ℝ) ^ j) K then E I else 0)
        (fun _ _ => by split_ifs <;> positivity) hj
      simpa only [if_pos hIj] using h
    _ = ∑ j ∈ Finset.range (lengthScale + 1), ∑ I ∈ highKernelRange M K,
        if I ∈ highKernelShellRange ((2 : ℝ) ^ j) K then E I else 0 := Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range (lengthScale + 1), ∑ I ∈ highKernelShellRange ((2 : ℝ) ^ j) K, E I := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro I hI
        exact (Finset.mem_filter.mp hI).2
      · intro I hI hnot
        exact hE I
    _ ≤ ∑ j ∈ Finset.range (lengthScale + 1), highKernelShellNorm ((2 : ℝ) ^ j) N K * ∑ J, ‖a J‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← Finset.sum_coe_sort (highKernelShellRange ((2 : ℝ) ^ j) K) E]
      exact FiniteSieveOperator.energy_bound (highKernelShellMatrix ((2 : ℝ) ^ j) N K) a
    _ = _ := (Finset.sum_mul ..).symm

end CanonicalQuadraticSieve

open scoped SchwartzMap ContDiff
namespace QuadraticInitialBound

def annularSieveBump : ContDiffBump (3 / 4 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def annularSieveCutoff : 𝓢(ℝ, ℂ) := by
  have hc : HasCompactSupport (fun t : ℝ => (annularSieveBump t : ℂ)) :=
    annularSieveBump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun t : ℝ => (annularSieveBump t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp annularSieveBump.contDiff
  exact hc.toSchwartzMap hs

@[simp] theorem annularSieveCutoff_apply (t : ℝ) : annularSieveCutoff t = (annularSieveBump t : ℂ) := rfl

theorem annularSieveBump_eq_one {t : ℝ} (ht0 : 1 / 2 ≤ t) (ht1 : t ≤ 1) : annularSieveBump t = 1 := by
  apply annularSieveBump.one_of_mem_closedBall
  change dist t (3 / 4) ≤ 1 / 4
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

theorem annularSieveBump_zero_of_le {t : ℝ} (ht : t ≤ 1 / 4) : annularSieveBump t = 0 := by
  apply annularSieveBump.zero_of_le_dist
  change 1 / 2 ≤ dist t (3 / 4)
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

theorem annularSieveBump_zero_of_ge {t : ℝ} (ht : 5 / 4 ≤ t) : annularSieveBump t = 0 := by
  apply annularSieveBump.zero_of_le_dist
  change 1 / 2 ≤ dist t (3 / 4)
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

@[simp] theorem annularSieveCutoff_zero : annularSieveCutoff 0 = 0 := by
  rw [annularSieveCutoff_apply, annularSieveBump_zero_of_le (by norm_num), Complex.ofReal_zero]

end QuadraticInitialBound

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy

def annularHighWeight (M : ℝ) (I : Ideal O) : ℝ :=
  QuadraticInitialBound.annularSieveBump ((Ideal.absNorm I : ℝ) / M)

def annularHighEnergy (M N K : ℝ) (a : idealRange N → ℂ) : ℝ :=
  ∑ I : highKernelRange (2 * M) K, annularHighWeight M I.val *
    ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2

theorem highKernelShell_energy_le_annular (M N K : ℝ) (hM : 0 < M) (a : idealRange N → ℂ) :
    (∑ I : highKernelShellRange M K, ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2) ≤
      annularHighEnergy M N K a := by
  let E : Ideal O → ℝ := fun I => ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖ ^ 2
  have hsub : highKernelShellRange M K ⊆ highKernelRange (2 * M) K := by
    intro I hI
    obtain ⟨hs, hn, hk⟩ := mem_highKernelRange.mp (mem_highKernelShellRange.mp hI).1
    exact mem_highKernelRange.mpr ⟨hs, by linarith, hk⟩
  have hv (I : Ideal O) (hI : I ∈ highKernelShellRange M K) : annularHighWeight M I = 1 := by
    apply QuadraticInitialBound.annularSieveBump_eq_one
    · apply (le_div_iff₀ hM).mpr
      have h := (mem_highKernelShellRange.mp hI).2
      linarith
    · exact (div_le_one hM).mpr (mem_highKernelRange.mp (mem_highKernelShellRange.mp hI).1).2.1
  change (∑ I : highKernelShellRange M K, E I.val) ≤
    ∑ I : highKernelRange (2 * M) K, annularHighWeight M I.val * E I.val
  rw [Finset.sum_coe_sort (highKernelShellRange M K) E,
    Finset.sum_coe_sort (highKernelRange (2 * M) K) (fun I => annularHighWeight M I * E I)]
  calc
    _ = ∑ I ∈ highKernelShellRange M K, annularHighWeight M I * E I :=
      Finset.sum_congr rfl (fun I hI => by rw [hv I hI, one_mul])
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun I hI hnot =>
      mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (sq_nonneg _))

def annularRayGcdBlock (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) : ℂ :=
  weightedRayGcdBlock D c (fun I : highKernelRange (2 * M) K => I.val)
    (fun J : idealRange N => J.val) (fun I => annularHighWeight M I.val) a

theorem highKernelShell_energy_annular_gcd_reduction (M N K G : ℝ)
    (hM : 0 < M) (hN : 1 ≤ N) (hG : 0 < G) (ε : ℝ) (hε : 0 < ε) (a : idealRange N → ℂ) :
    (∑ I : highKernelShellRange M K, ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2) ≤
      16 * ((∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖annularRayGcdBlock M N K D c a‖) +
        highKernelNorm (2 * M) (N / G) K * (supportConstant ε hε * divisorConstant ε hε) *
          (N ^ ε) ^ 2 * ∑ J, ‖a J‖ ^ 2) := by
  apply (highKernelShell_energy_le_annular M N K hM a).trans
  have h := highKernel_weighted_energy_ray_gcd_reduction ε hε G hG
    (fun I : highKernelRange (2 * M) K => I.val) (fun J : idealRange N => J.val)
    Subtype.val_injective Subtype.val_injective (2 * M) N K hN (fun I => I.property)
    (fun J => mem_idealRange.mp J.property) (fun I => annularHighWeight M I.val) 1 (by norm_num)
    (fun I => ⟨QuadraticInitialBound.annularSieveBump.nonneg, QuadraticInitialBound.annularSieveBump.le_one⟩) a
  simpa only [annularHighEnergy, annularRayGcdBlock, one_mul] using h

end

section
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator
open IdealCoprimeSieveOperator DivisorBlockCauchy FiniteSieveRestriction

theorem annularRayGcdBlock_norm_le (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    ‖annularRayGcdBlock M N K D c a‖ ≤
      ‖operator (weightedRayGramMatrix D c (fun I : highKernelRange (2 * M) K => I.val)
        (fun J : idealRange N => J.val) (fun I => annularHighWeight M I.val))‖ * ∑ J, ‖a J‖ ^ 2 := by
  unfold annularRayGcdBlock
  rw [weightedRayGcdBlock_eq_quadraticForm]
  exact quadratic_form_bound _ _

def annularRayThirdNorm (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) : ℝ :=
  sSup (Set.range (fun a : idealRange N → ℂ =>
    ‖annularRayGcdBlock M N K D c a‖ / (∑ J, ‖a J‖ ^ 2)))

def annularThirdNorm (M N K : ℝ) (D : Ideal O) : ℝ :=
  ∑ c : EisensteinEPrimaryPhase.Coord, annularRayThirdNorm M N K D c

theorem annularRayThirdNorm_bddAbove (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    BddAbove (Set.range (fun a : idealRange N → ℂ =>
      ‖annularRayGcdBlock M N K D c a‖ / (∑ J, ‖a J‖ ^ 2))) := by
  refine ⟨‖operator (weightedRayGramMatrix D c (fun I : highKernelRange (2 * M) K => I.val)
    (fun J : idealRange N => J.val) (fun I => annularHighWeight M I.val))‖, ?_⟩
  rintro x ⟨a, rfl⟩
  dsimp only
  have he : 0 ≤ ∑ J, ‖a J‖ ^ 2 := by positivity
  rcases he.eq_or_lt with he | he
  · rw [← he, div_zero]
    exact norm_nonneg _
  · exact (div_le_iff₀ he).mpr (annularRayGcdBlock_norm_le M N K D c a)

theorem annularRayThirdNorm_nonneg (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) :
    0 ≤ annularRayThirdNorm M N K D c := by
  unfold annularRayThirdNorm
  apply le_csSup (annularRayThirdNorm_bddAbove M N K D c)
  refine ⟨(fun _ => 0), ?_⟩
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, div_zero]

theorem annularThirdNorm_nonneg (M N K : ℝ) (D : Ideal O) : 0 ≤ annularThirdNorm M N K D :=
  Finset.sum_nonneg (fun c _ => annularRayThirdNorm_nonneg M N K D c)

theorem annularRayThirdNorm_bound (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    ‖annularRayGcdBlock M N K D c a‖ ≤ annularRayThirdNorm M N K D c * ∑ J, ‖a J‖ ^ 2 := by
  have he : 0 ≤ ∑ J, ‖a J‖ ^ 2 := by positivity
  rcases he.eq_or_lt with he | he
  · have hb := annularRayGcdBlock_norm_le M N K D c a
    simpa only [← he, mul_zero] using hb
  · exact (div_le_iff₀ he).mp (le_csSup (annularRayThirdNorm_bddAbove M N K D c) (Set.mem_range_self a))

theorem highKernelShellNorm_le_annularThirdNorm (M N K G : ℝ)
    (hM : 0 < M) (hN : 1 ≤ N) (hG : 0 < G) (ε : ℝ) (hε : 0 < ε) :
    highKernelShellNorm M N K ≤ 16 *
      ((∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          annularThirdNorm M N K D) +
        highKernelNorm (2 * M) (N / G) K * (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2) := by
  apply squared_norm_le_of_energy _ _
  · have hb := highKernelNorm_nonneg (2 * M) (N / G) K
    have hs := (supportConstant_pos ε hε).le
    have hd := (divisorConstant_pos ε hε).le
    have ht : 0 ≤ ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
        annularThirdNorm M N K D := Finset.sum_nonneg (fun D _ => annularThirdNorm_nonneg M N K D)
    positivity
  · intro a
    have h := highKernelShell_energy_annular_gcd_reduction M N K G hM hN hG ε hε a
    apply h.trans
    have hsum : (∑ c : EisensteinEPrimaryPhase.Coord,
        ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          ‖annularRayGcdBlock M N K D c a‖) ≤
        (∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          annularThirdNorm M N K D) * ∑ J, ‖a J‖ ^ 2 := by
      calc
        _ ≤ ∑ c : EisensteinEPrimaryPhase.Coord,
            ∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
              annularRayThirdNorm M N K D c * ∑ J, ‖a J‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro c _
          exact Finset.sum_le_sum (fun D _ => annularRayThirdNorm_bound M N K D c a)
        _ = _ := by rw [Finset.sum_comm]; simp only [annularThirdNorm, Finset.sum_mul]
    nlinarith

end

open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction
open QuadraticSquarefreeKernel

theorem annularHighWeight_eq_zero (M : ℝ) (hM : 0 < M) (I : Ideal O)
    (hI : 2 * M ≤ (Ideal.absNorm I : ℝ)) : annularHighWeight M I = 0 := by
  have ht : 2 ≤ (Ideal.absNorm I : ℝ) / M := (le_div_iff₀ hM).mpr (by linarith)
  exact QuadraticInitialBound.annularSieveBump_zero_of_ge (by linarith)

theorem annularRayGcdBlock_eq_finite (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑ I : highKernelRange (2 * M) K, (annularHighWeight M I.val : ℂ) * rayPairValue N D c a I.val := by
  rfl

theorem annularRayGcdBlock_eq_tsum (M N K : ℝ) (hM : 0 < M)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (a : idealRange N → ℂ) :
    annularRayGcdBlock M N K D c a =
      ∑' I : Ideal O, if Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) then
        QuadraticInitialBound.annularSieveCutoff ((Ideal.absNorm I : ℝ) / M) * rayPairValue N D c a I else 0 := by
  rw [annularRayGcdBlock_eq_finite,
    Finset.sum_coe_sort (highKernelRange (2 * M) K) (fun I => (annularHighWeight M I : ℂ) * rayPairValue N D c a I)]
  symm
  rw [tsum_eq_sum (s := highKernelRange (2 * M) K) (fun I hI => ?_)]
  · apply Finset.sum_congr rfl
    intro I hI
    have hp : Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) := by
      have h := mem_highKernelRange.mp hI
      exact ⟨h.1, h.2.2⟩
    rw [if_pos hp, QuadraticInitialBound.annularSieveCutoff_apply]
    rfl
  · by_cases hp : Supported I ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ)
    · have hn : 2 * M < (Ideal.absNorm I : ℝ) := by
        by_contra hh
        exact hI (mem_highKernelRange.mpr ⟨hp.1, le_of_not_gt hh, hp.2⟩)
      rw [if_pos hp, QuadraticInitialBound.annularSieveCutoff_apply]
      change (annularHighWeight M I : ℂ) * _ = 0
      rw [annularHighWeight_eq_zero M hM I hn.le]
      simp
    · exact if_neg hp

end CanonicalQuadraticSieve

namespace FiniteSieveOperator

theorem bounded_entry_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) (hA : ∀ i j, ‖A i j‖ ≤ 1) :
    ‖operator A‖ ^ 2 ≤ (Fintype.card m : ℝ) * Fintype.card n := by
  apply squared_norm_le_of_energy _ _ (by positivity)
  intro a
  have hi (i : m) : ‖∑ j, A i j * a j‖ ^ 2 ≤ (Fintype.card n : ℝ) * ∑ j, ‖a j‖ ^ 2 := by
    have hs : ‖∑ j, A i j * a j‖ ≤ ∑ j, ‖a j‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hA i j)
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : n => (1 : ℝ)) (fun j => ‖a j‖)
    exact (pow_le_pow_left₀ (norm_nonneg _) hs 2).trans (by simpa using hc)
  calc
    _ ≤ ∑ i : m, (Fintype.card n : ℝ) * ∑ j, ‖a j‖ ^ 2 := Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
end FiniteSieveOperator

namespace CanonicalQuadraticSieve

section
open FiniteSieveOperator

theorem highKernelNorm_trivial (M N K : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    highKernelNorm M N K ≤ 128 ^ 2 * M * N := by
  have hr := DescentFiberCost.finite_ideal_count_real (highKernelRange M K) M hM
    (fun I hI => (mem_highKernelRange.mp hI).1.1)
    (fun I hI => (mem_highKernelRange.mp hI).2.1)
  have hc := DescentFiberCost.finite_ideal_count_real (idealRange N) N hN
    (fun I hI => (mem_idealRange.mp hI).1.1)
    (fun I hI => (mem_idealRange.mp hI).2)
  have hb := bounded_entry_squared_norm_le (highKernelMatrix M N K)
    (fun I J => quadraticRow_norm_le_one J.val _)
  change highKernelNorm M N K ≤ _ at hb
  apply hb.trans
  simp only [Fintype.card_coe]
  calc
    _ ≤ (128 * M) * (128 * N) := mul_le_mul hr hc (by positivity) (by positivity)
    _ = _ := by ring

theorem highKernelNorm_short_columns (M N K : ℝ) (hM : 1 ≤ M) (hN : N ≤ 1) :
    highKernelNorm M N K ≤ 128 ^ 2 * M := by
  exact (highKernelNorm_mono (M := M) (K := K) le_rfl hN le_rfl).trans
    (by simpa only [mul_one] using highKernelNorm_trivial M 1 K hM le_rfl)

end

open IdealCoprimeSieveOperator DivisorBlockCauchy

theorem highKernelNorm_le_annular_recursion (M N K G : ℝ) (lengthScale : ℕ)
    (hML : M ≤ (2 : ℝ) ^ lengthScale) (hN : 1 ≤ N) (hG : 0 < G) (ε : ℝ) (hε : 0 < ε) :
    highKernelNorm M N K ≤ 16 * ∑ j ∈ Finset.range (lengthScale + 1),
      ((∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          annularThirdNorm ((2 : ℝ) ^ j) N K D) +
        highKernelNorm (2 * (2 : ℝ) ^ j) (N / G) K *
          (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2) := by
  apply (highKernelNorm_le_dyadic_shells M N K lengthScale hML).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j hj => highKernelShellNorm_le_annularThirdNorm
    ((2 : ℝ) ^ j) N K G (by positivity) hN hG ε hε)

theorem sieveNorm_le_annular_recursion (M N K G : ℝ) (lengthScale : ℕ)
    (hML : M ≤ (2 : ℝ) ^ lengthScale) (hN : 1 ≤ N) (hG : 0 < G) (ε : ℝ) (hε : 0 < ε) :
    sieveNorm M N ≤ sieveNorm K N + 16 * ∑ j ∈ Finset.range (lengthScale + 1),
      ((∑ D ∈ (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ G),
          annularThirdNorm ((2 : ℝ) ^ j) N K D) +
        highKernelNorm (2 * (2 : ℝ) ^ j) (N / G) K *
          (supportConstant ε hε * divisorConstant ε hε) * (N ^ ε) ^ 2) := by
  exact (sieveNorm_le_low_add_high M N K).trans
    (add_le_add le_rfl (highKernelNorm_le_annular_recursion M N K G lengthScale hML hN hG ε hε))

end CanonicalQuadraticSieve

end

end OAI

end



-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0065_1
-- name    : PNT_ZeroFree_433_0065_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T16:32:12.214654+00:00
-- url     : https://prove2.me/theorems/87a037ec-7299-455a-9820-6cf4a9691f4b
-- title:
--   Zero-free region foundations: QuadraticSieve.IdealQuotients [0065_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.IdealQuotients
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/IdealQuotients.lean#L80-L409

import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0064

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/IdealQuotients.lean
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss ConcreteTraceCRT

theorem primaryGenerator_admissible (I : Ideal O) (hI : Admissible I) : primaryGenerator I ≠ 0 :=
  PrimaryIdealUnitReindex.primaryGenerator_ne_zero_of_good_factors I hI.1
    (fun P hP => (hI.2.2 P hP).1)

theorem primaryGenerator_inj_on_admissible {I J : Ideal O}
    (hI : Admissible I) (hJ : Admissible J) (heq : primaryGenerator I = primaryGenerator J) : I = J := by
  calc
    I = Ideal.span {primaryGenerator I} := (primaryGenerator_spec I (primaryGenerator_admissible I hI)).1.symm
    _ = Ideal.span {primaryGenerator J} := by rw [heq]
    _ = J := (primaryGenerator_spec J (primaryGenerator_admissible J hJ)).1

theorem sieveNorm_initial (M N : ℝ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    sieveNorm M N ≤ QuadraticInitialBound.initialSieveConstant * (M + (⌈N⌉₊ : ℝ) ^ 2) := by
  let F := idealRange N
  let R := (idealRange M).image primaryGenerator
  have hF : ∀ I ∈ F, Admissible I := fun I hI => (mem_idealRange.mp hI).1
  have hFp : ∀ I ∈ F, I ≠ ⊥ := fun I hI => (hF I hI).1
  have hFg : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P :=
    fun I hI P hP => (hF I hI).2.2 P hP |>.1
  have hchar : ∀ i : primePool F, ringChar (O ⧸ i.val) ≠ 2 := by
    intro i
    obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp i.property
    exact (hF I hI).2.2 i.val hP |>.2
  have hnat : 1 ≤ ⌈N⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ ⌈N⌉₊ := by
    intro I hI
    exact Nat.cast_le.mp ((mem_idealRange.mp hI).2.trans (Nat.le_ceil N))
  have hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M := by
    intro z hz
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hz
    rw [primaryGenerator_norm_sq I (primaryGenerator_admissible I (mem_idealRange.mp hI).1)]
    exact (mem_idealRange.mp hI).2
  have hgen : Set.InjOn primaryGenerator (idealRange M) := by
    intro I hI J hJ heq
    exact primaryGenerator_inj_on_admissible (mem_idealRange.mp hI).1 (mem_idealRange.mp hJ).1 heq
  apply FiniteSieveOperator.squared_norm_le_of_energy (matrix M N)
  · have hc := (QuadraticInitialBound.initialSieveConstant_pos).le
    positivity
  intro a
  let aext (I : Ideal O) : ℂ := if h : I ∈ F then a ⟨I, h⟩ else 0
  have hinner (z : O) :
      (∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 3) =
        ∑ J : F, quadraticRow J.val z * a J := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    rw [quadraticRow_eq F hF J.val J.property z]
    simp only [aext, dif_pos J.property]
    change a J * (idealSexticRow F hFp hFg J.val z) ^ 3 =
      (idealSexticRow F hFp hFg J.val z) ^ 3 * a J
    exact mul_comm _ _
  have he := QuadraticInitialBound.ideal_initial_quadratic_sieve F hFp hFg
    (fun I hI => (hF I hI).2.1) hchar ⌈N⌉₊ hnat hnorm aext M hM R hR
  have heR : (∑ z ∈ R, ‖∑ I ∈ F, aext I * (idealSexticRow F hFp hFg I z) ^ 3‖ ^ 2) =
      ∑ I : idealRange M, ‖∑ J : F, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2 := by
    dsimp only [R]
    rw [Finset.sum_image (fun I hI J hJ heq => hgen hI hJ heq)]
    simp_rw [hinner]
    exact (Finset.sum_coe_sort _ _).symm
  have hea : (∑ I ∈ F, ‖aext I‖ ^ 2) = ∑ J : F, ‖a J‖ ^ 2 := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro J _
    simp only [aext, dif_pos J.property]
    rfl
  rw [heR, hea] at he
  exact he

end

open ActualEisensteinCubic CompletedGauss

def idealQuotient (D I : Ideal O) : Ideal O := if h : D ∣ I then h.choose else 0

theorem idealQuotient_mul {D I : Ideal O} (h : D ∣ I) : D * idealQuotient D I = I := by
  rw [idealQuotient, dif_pos h]
  exact h.choose_spec.symm

theorem idealQuotient_dvd {D I : Ideal O} (h : D ∣ I) : idealQuotient D I ∣ I := by
  refine ⟨D, ?_⟩
  rw [mul_comm, idealQuotient_mul h]

theorem idealQuotient_injective_on (D : Ideal O) :
    Set.InjOn (idealQuotient D) {I | D ∣ I} := by
  intro I hI J hJ heq
  calc
    I = D * idealQuotient D I := (idealQuotient_mul hI).symm
    _ = D * idealQuotient D J := by rw [heq]
    _ = J := idealQuotient_mul hJ

theorem admissible_of_dvd {I J : Ideal O} (hI : Admissible I) (hJI : J ∣ I) : Admissible J := by
  have hJ : J ≠ 0 := ne_zero_of_dvd_ne_zero hI.1 hJI
  refine ⟨hJ, hI.2.1.squarefree_of_dvd hJI, ?_⟩
  intro P hP
  have hfac := (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hJ hI.1).mp hJI
  exact hI.2.2 P (Multiset.mem_of_le hfac hP)

theorem admissible_idealQuotient {D I : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible (idealQuotient D I) := admissible_of_dvd hI (idealQuotient_dvd hD)

theorem idealQuotient_norm_le {D I : Ideal O} (hD0 : D ≠ 0) (hD : D ∣ I)
    (N : ℝ) (hN : (Ideal.absNorm I : ℝ) ≤ N) :
    (Ideal.absNorm (idealQuotient D I) : ℝ) ≤ N / (Ideal.absNorm D : ℝ) := by
  have hp : (0 : ℝ) < Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hD0 (Ideal.absNorm_eq_zero_iff.mp h))
  apply (le_div_iff₀ hp).mpr
  calc
    _ = (Ideal.absNorm (D * idealQuotient D I) : ℝ) := by
      rw [map_mul, Nat.cast_mul, mul_comm]
    _ = (Ideal.absNorm I : ℝ) := by rw [idealQuotient_mul hD]
    _ ≤ N := hN

theorem quotient_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hdiv : ∀ j, D ∣ cols j) (M N : ℝ)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (fun i j =>
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)))‖ ^ 2 ≤
      sieveNorm M (N / (Ideal.absNorm D : ℝ)) := by
  apply family_squared_norm_le rows (fun j => idealQuotient D (cols j)) hr
  · intro j k heq
    exact hc (idealQuotient_injective_on D (hdiv j) (hdiv k) heq)
  · exact hrows
  · intro j
    exact ⟨admissible_idealQuotient (hcols j).1 (hdiv j),
      idealQuotient_norm_le hD (hdiv j) N (hcols j).2⟩

def quotientMatrix {m n : Type*} (D : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O) :
    Matrix m n ℂ := fun i j => if D ∣ cols j then
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) else 0

theorem quotientMatrix_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols) (M N : ℝ)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (quotientMatrix D rows cols)‖ ^ 2 ≤
      sieveNorm M (N / (Ideal.absNorm D : ℝ)) := by
  let S : Finset n := Finset.univ.filter (fun j => D ∣ cols j)
  let A : Matrix m S ℂ := fun i j =>
    quadraticRow (idealQuotient D (cols j.val)) (primaryGenerator (rows i))
  have hnorm : ‖FiniteSieveOperator.operator A‖ ^ 2 ≤
      sieveNorm M (N / (Ideal.absNorm D : ℝ)) := by
    apply quotient_family_squared_norm_le D hD rows (fun j : S => cols j.val) hr
      (hc.comp Subtype.val_injective)
    · intro j
      exact (Finset.mem_filter.mp j.property).2
    · exact hrows
    · intro j
      exact hcols j.val
  apply FiniteSieveOperator.squared_norm_le_of_energy _ _ (sieveNorm_nonneg _ _)
  intro a
  have hinner (i : m) : (∑ j, quotientMatrix D rows cols i j * a j) =
      ∑ j : S, A i j * a j.val := by
    change (∑ j, (if D ∣ cols j then
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) else 0) * a j) =
      ∑ j : S, quadraticRow (idealQuotient D (cols j.val)) (primaryGenerator (rows i)) * a j.val
    rw [Finset.sum_coe_sort S (fun j : n =>
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) * a j)]
    simp only [S, Finset.sum_filter, ite_mul, zero_mul]
  simp_rw [hinner]
  have henergy := FiniteSieveOperator.energy_bound A (fun j : S => a j.val)
  apply henergy.trans
  calc
    _ ≤ sieveNorm M (N / (Ideal.absNorm D : ℝ)) * ∑ j : S, ‖a j.val‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hnorm (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sieveNorm_nonneg _ _)
      rw [Finset.sum_coe_sort S (fun j : n => ‖a j‖ ^ 2)]
      exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖a j‖)

end CanonicalQuadraticSieve

section
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
namespace FourierBridge

def fourierSeminormBound (k : ℕ) (C : ℝ) : ℝ :=
  (2 : ℝ) ^ k * (k + 1) *
    (2 ^ (volume : Measure ℝ).integrablePower *
      ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C

def fourierPointBound (k : ℕ) (C : ℝ) : ℝ :=
  2 ^ k * (fourierSeminormBound 0 C + fourierSeminormBound k C)

theorem fourierPointBound_nonneg (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ fourierPointBound k C := by unfold fourierPointBound fourierSeminormBound; positivity

theorem uniform_fourier_pointwise (g : 𝓢(ℝ, ℂ)) (k : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ k,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C)
    (t : ℝ) :
    S * (1 + ‖t‖) ^ k * ‖(𝓕 g) t‖ ≤ fourierPointBound k C := by
  have h0 : S * (SchwartzMap.seminorm ℝ 0 0) (𝓕 g) ≤ fourierSeminormBound 0 C :=
    uniform_fourier_seminorm_transfer g 0 S C hS hC
      (fun i hi => hsource i (hi.trans (Nat.zero_le k)))
  have hk : S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤ fourierSeminormBound k C :=
    uniform_fourier_seminorm_transfer g k S C hS hC hsource
  have hpow : (1 + ‖t‖) ^ k ≤ (2 : ℝ) ^ k * (1 + ‖t‖ ^ k) := by
    have h := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg t) k
    have he : (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)
    simp only [one_pow] at h
    exact h.trans (mul_le_mul_of_nonneg_right he (by positivity))
  have hn0 := SchwartzMap.norm_le_seminorm ℝ (𝓕 g) t
  have hnk := SchwartzMap.norm_pow_mul_le_seminorm ℝ (𝓕 g) k t
  calc
    _ ≤ S * ((2 : ℝ) ^ k * (1 + ‖t‖ ^ k)) * ‖(𝓕 g) t‖ := by gcongr
    _ = (2 : ℝ) ^ k * (S * ‖(𝓕 g) t‖ + S * (‖t‖ ^ k * ‖(𝓕 g) t‖)) := by ring
    _ ≤ (2 : ℝ) ^ k * (S * (SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
          S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g)) := by gcongr
    _ ≤ fourierPointBound k C := by
      exact mul_le_mul_of_nonneg_left (add_le_add h0 hk) (by positivity)

end FourierBridge

namespace LocalLogFourier

theorem coupled_positive_log_separation_envelope
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F : ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (A J : ℕ) (CF : ℝ) (hCF : 0 ≤ CF)
    (hEuler : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
        (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  classical
  let T : ℝ := ∑ j : ι, |a j| * M j
  have hT : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (abs_nonneg _) (hM j)
  let K : ℕ := J + (volume : Measure ℝ).integrablePower
  let Lwin : ℝ := T + 1
  let m : ℝ := Real.exp (-Lwin)
  have hL : 0 ≤ Lwin := by dsimp [Lwin]; linarith
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    simpa using (Real.exp_le_exp.mpr (show -Lwin ≤ 0 by linarith))
  obtain ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, hwindow⟩ :=
    FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  let P : ℝ := momentConstant K Lwin CW CF
  let B : ℝ := (2 : ℝ) ^ J *
    (FourierBridge.coefficientMomentBound 0 P +
      FourierBridge.coefficientMomentBound J P)
  let Bpoint : ℝ := FourierBridge.fourierPointBound J P
  let C : ℝ := (B + Bpoint) / m ^ A
  have hP : 0 ≤ P := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity)
      (add_nonneg
        (FourierBridge.coefficientMomentBound_nonneg 0 P hP)
        (FourierBridge.coefficientMomentBound_nonneg J P hP))
  have hBpoint : 0 ≤ Bpoint := FourierBridge.fourierPointBound_nonneg J P hP
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R hR
  let b : 𝓢(ℝ, ℂ) := 𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 →
        V (∑ j : ι, a j * y j) = 1 :=
      FourierBridge.coupled_cutoff_active W V a y M hWwindow
        (by simpa [T] using hVone)
    simpa [b] using coupled_positive_log_separation W F V R a y
      hVc hVs hFpos hR hactive
  · exact AnalyticBridge.schwartz_fourier_one_plus_integrable
      (positiveLogProfile V F R hVc hVs hFpos hR) J
  · have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hbound := positive_log_fourier_bound V F R m Lwin CW CF A J
      hVc hVs hFpos hR hm hm1 hL hCW hCF
      (by simpa [K] using hVderiv)
      (by simpa only [K] using hwindow')
      (by simpa [K] using hEuler)
    have hb : (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ B / m ^ A := by
      simpa [B, P, b, K, Lwin, m] using hbound
    exact hb.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right hBpoint) (by positivity))
  · intro t
    let g := positiveLogProfile V F R hVc hVs hFpos hR
    have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hsource (n : ℕ) (hn : n ≤ J) :
        (m ^ A * (1 + R) ^ A) *
          ((SchwartzMap.seminorm ℝ 0 n) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n) g) ≤ P := by
      apply positive_log_source_pair V F R m Lwin CW CF P A K n
        hVc hVs hFpos hR hm hm1 hL hCW hCF
      · dsimp [K]; omega
      · exact hVderiv
      · exact hwindow'
      · exact hEuler
      · intro i hi
        exact momentConstant_dominates K i Lwin CW CF hL hCW hCF hi
    have hpoint := FourierBridge.uniform_fourier_pointwise g J
      (m ^ A * (1 + R) ^ A) P (by positivity) hP hsource t
    have hb : (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ Bpoint / m ^ A := by
      apply (le_div_iff₀ (pow_pos hm A)).mpr
      simpa only [g, b, Bpoint, mul_assoc, mul_left_comm, mul_comm] using hpoint
    exact hb.trans (div_le_div_of_nonneg_right (le_add_of_nonneg_left hB) (by positivity))

end LocalLogFourier

namespace EisensteinSchwartzPoisson


end EisensteinSchwartzPoisson
end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportRay supportIdealFamily supportIdealFamily_pos
  supportIdealFamily_good recoveredSupport)
open ConcretePrimeRowBridge (conjugateIdealRowSum)
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)


end FirstPassCubeLabels

end

end OAI

end



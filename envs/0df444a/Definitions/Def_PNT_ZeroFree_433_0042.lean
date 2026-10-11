-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0042
-- name    : PNT_ZeroFree_433_0042
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T14:33:24.798435+00:00
-- url     : https://prove2.me/theorems/7f60f731-2ec6-4211-8c8f-e8ad0cfef281
-- title:
--   Zero-free region foundations: Poisson.RadialFourier [0042]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Poisson.RadialFourier
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/RadialFourier.lean#L350-L619

import Definitions.Def_PNT_ZeroFree_433_0042_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Poisson/RadialFourier.lean
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

namespace EisensteinSchwartzPoisson

section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff


end

section
open MeasureTheory
open scoped SchwartzMap ContDiff


theorem paperRadialFourier_euler_weighted_bound (W : 𝓢(ℝ, ℂ)) (A j : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤
      2 ^ A * (SchwartzMap.seminorm ℝ 0 0 (paperEulerCLM j W) +
        SchwartzMap.seminorm ℝ (2 * A) 0 (paperEulerCLM j W)) := by
  rw [paperRadialFourier_eulerDeriv W j x hx]
  exact sqrt_profile_rapid_bound _ A x hx

theorem schwartzCLM_family_finite_seminorm_control
    (T : ℕ → 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)) (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (j : ℕ), j ≤ K →
        SchwartzMap.seminorm ℝ 0 0 (T j W) +
          SchwartzMap.seminorm ℝ (2 * A) 0 (T j W) ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let qj : ℕ → Seminorm ℝ 𝓢(ℝ, ℂ) := fun j =>
    (SchwartzMap.seminorm ℝ 0 0 + SchwartzMap.seminorm ℝ (2 * A) 0).comp
      (T j).toLinearMap
  let q : Seminorm ℝ 𝓢(ℝ, ℂ) := ∑ j ∈ Finset.range (K + 1), qj j
  have hqfun : (q : 𝓢(ℝ, ℂ) → ℝ) = fun W => ∑ j ∈ Finset.range (K + 1),
      (SchwartzMap.seminorm ℝ 0 0 (T j W) +
        SchwartzMap.seminorm ℝ (2 * A) 0 (T j W)) := by
    funext W
    simp [q, qj]
  have hq : Continuous q := by
    rw [hqfun]
    apply continuous_finsetSum
    intro j hj
    exact (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (0, 0)).comp
        (T j).continuous).add
      (((schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm (2 * A, 0)).comp
        (T j).continuous)
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) q hq
  refine ⟨s, C, ?_, ?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W j hj
    apply le_trans ?_ (Seminorm.le_def.mp hbound W)
    rw [hqfun]
    exact Finset.single_le_sum (f := fun i =>
      SchwartzMap.seminorm ℝ 0 0 (T i W) +
        SchwartzMap.seminorm ℝ (2 * A) 0 (T i W))
      (by intro i hi; positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem paperRadialFourier_euler_source_weighted_bound (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (j : ℕ), j ≤ K → ∀ (x : ℝ), 0 ≤ x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hbound⟩ :=
    schwartzCLM_family_finite_seminorm_control paperEulerCLM A K
  refine ⟨s, 2 ^ A * C, by positivity, ?_⟩
  intro W j hj x hx
  apply (paperRadialFourier_euler_weighted_bound W A j x hx).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hbound W j hj) (show 0 ≤ (2 : ℝ) ^ A by positivity)

theorem paperRadialFourier_euler_source_decay (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (j : ℕ), j ≤ K → ∀ (x : ℝ), 0 ≤ x →
        ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + x) ^ A := by
  obtain ⟨s, C, hC, hbound⟩ := paperRadialFourier_euler_source_weighted_bound A K
  refine ⟨s, C, hC, ?_⟩
  intro W j hj x hx
  apply (le_div_iff₀ (by positivity : 0 < (1 + x) ^ A)).mpr
  simpa only [mul_comm] using hbound W j hj x hx

theorem paperRadialFourier_euler_bound (W : 𝓢(ℝ, ℂ)) (A K : ℕ) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ j ≤ K, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤ CF := by
  obtain ⟨s, C, hC, hbound⟩ := paperRadialFourier_euler_source_weighted_bound A K
  refine ⟨C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W, by positivity, ?_⟩
  intro j hj x hx
  exact hbound W j hj x hx.le

theorem compact_paperRadialFourier_regular
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (A K : ℕ) :
    ContDiffOn ℝ ∞ (paperRadialFourier W) (Set.Ioi 0) ∧
      ∃ CF : ℝ, 0 ≤ CF ∧ ∀ j ≤ K, ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤ CF := by
  exact ⟨paperRadialFourier_contDiffOn (hWc.toSchwartzMap hWs),
    paperRadialFourier_euler_bound (hWc.toSchwartzMap hWs) A K⟩

theorem paperRadialFourier_log_separation
    {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hVwindow : ∀ j z, V j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : ℝ → ℂ,
        (∀ y : ι → ℝ,
          (∏ j : ι, V j (y j)) *
            paperRadialFourier W (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, V j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C := by
  obtain ⟨CF, hCF, hEuler⟩ := paperRadialFourier_euler_bound W A
    (J + (MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower)
  exact LocalLogFourier.coupled_positive_log_separation_uniform V (paperRadialFourier W)
    a M hM hVwindow (paperRadialFourier_contDiffOn W) A J CF hCF hEuler

end

open ConcreteTraceCRT ActualEisensteinCubic
open scoped SchwartzMap

theorem inverse_square_le_cauchy_product (a b q : ℝ) (hq : 0 ≤ q)
    (hQ : (a ^ 2 + b ^ 2) / 2 ≤ q) :
    ((1 + q) ^ 2)⁻¹ ≤
      4 * ((1 + a ^ 2)⁻¹ * (1 + b ^ 2)⁻¹) := by
  have hsum : 1 + a ^ 2 + b ^ 2 ≤ 2 * (1 + q) := by linarith
  have hsquare : (1 + a ^ 2 + b ^ 2) ^ 2 ≤ (2 * (1 + q)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hsum
  have hden : (1 + a ^ 2) * (1 + b ^ 2) ≤ 4 * (1 + q) ^ 2 := by
    nlinarith [sq_nonneg (a ^ 2), sq_nonneg (b ^ 2),
      mul_nonneg (sq_nonneg a) (sq_nonneg b)]
  calc
    _ = 1 / (1 + q) ^ 2 := by simp only [one_div]
    _ ≤ 4 / ((1 + a ^ 2) * (1 + b ^ 2)) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hden)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem eisenstein_cauchy_summable :
    Summable (fun h : O => ((1 + ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) := by
  apply (latticeCoordEquiv.symm.summable_iff).mp
  change Summable (fun p : ℤ × ℤ =>
    ((1 + ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) ^ 2)⁻¹)
  apply Summable.of_nonneg_of_le (fun _ => inv_nonneg.mpr (sq_nonneg _)) _
    (summable_int_cauchy_product.mul_left 4)
  intro p
  apply inverse_square_le_cauchy_product (p.1 : ℝ) (p.2 : ℝ)
    (‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) (sq_nonneg _)
  change ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) / 2 ≤
    ‖eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2)‖ ^ 2
  rw [eisEmbedding_eval_norm_sq]
  push_cast
  nlinarith [sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ))]

def eisensteinCauchyMass : ℝ :=
  ∑' h : O, ((1 + ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹

theorem eisensteinCauchyMass_nonneg : 0 ≤ eisensteinCauchyMass :=
  tsum_nonneg (fun _ => by positivity)

theorem eisensteinCauchyMass_subtype (S : Set O) :
    (∑' h : S, ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) ≤ eisensteinCauchyMass := by
  exact (eisenstein_cauchy_summable.subtype S).tsum_le_tsum_of_inj
    Subtype.val Subtype.val_injective (fun _ _ => by positivity) (fun _ => le_rfl)
    eisenstein_cauchy_summable

theorem polynomial_tail_majorant (A : ℕ) (K T q B f : ℝ)
    (hK : 0 < K) (hT : 0 ≤ T) (hq : 0 ≤ q) (hf : 0 ≤ f)
    (htail : T ≤ K * q) (hbound : (1 + K * q) ^ (A + 2) * f ≤ B) :
    f ≤ (B / ((min 1 K) ^ 2 * (1 + T) ^ A)) * ((1 + q) ^ 2)⁻¹ := by
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hm1 : min 1 K ≤ 1 := min_le_left _ _
  have hmK : min 1 K ≤ K := min_le_right _ _
  have hbase : min 1 K * (1 + q) ≤ 1 + K * q := by
    nlinarith [mul_le_mul_of_nonneg_right hmK hq]
  have htwo : (min 1 K) ^ 2 * (1 + q) ^ 2 ≤ (1 + K * q) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hpow : (1 + T) ^ A ≤ (1 + K * q) ^ A :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hden : ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2 ≤
      (1 + K * q) ^ (A + 2) := by
    have hh := mul_le_mul hpow htwo (by positivity) (by positivity)
    rw [pow_add]
    nlinarith
  have hprod : f * (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) ≤ B := by
    calc
      _ = (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) * f := mul_comm _ _
      _ ≤ (1 + K * q) ^ (A + 2) * f := mul_le_mul_of_nonneg_right hden hf
      _ ≤ B := hbound
  have hraw := (le_div_iff₀ (show 0 < ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2
      by positivity)).mpr hprod
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hraw

theorem paperRadialFourier_lattice_summable_norm (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ‖paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + (0 : ℝ)) ^ (0 : ℕ)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (eisenstein_cauchy_summable.mul_left (B / D))
  intro h
  exact polynomial_tail_majorant 0 K 0 _ B _ hK (by norm_num)
    (sq_nonneg _) (norm_nonneg _) (by positivity) (hb W _ (by positivity))

theorem paperRadialFourier_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T : ℝ), 0 < K → 0 ≤ T →
        (∑' h : {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2},
          ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
        (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound (A + 2)
  refine ⟨s, C * (eisensteinCauchyMass + 1), by
    have := eisensteinCauchyMass_nonneg
    positivity, ?_⟩
  intro W K T hK hT
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + T) ^ A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hD : 0 < D := by dsimp [D]; positivity
  let S := {h : O | T ≤ K * ‖eisEmbedding h‖ ^ 2}
  have hp (h : S) :
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        (B / D) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
    exact polynomial_tail_majorant A K T _ B _ hK hT (sq_nonneg _)
      (norm_nonneg _) h.property (hb W _ (by positivity))
  have hmajor : Summable (fun h : S => (B / D) *
      ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
    (eisenstein_cauchy_summable.subtype S).mul_left (B / D)
  have hs : Summable (fun h : S =>
      ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp hmajor
  calc
    _ ≤ ∑' h : S, (B / D) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ :=
      hs.tsum_le_tsum hp hmajor
    _ = (B / D) * ∑' h : S, ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
    _ ≤ (B / D) * eisensteinCauchyMass :=
      mul_le_mul_of_nonneg_left (eisensteinCauchyMass_subtype S) (div_nonneg hB hD.le)
    _ ≤ (B / D) * (eisensteinCauchyMass + 1) := by
      gcongr
      linarith
    _ = _ := by dsimp [B, D]; ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical SchwartzMap ContDiff

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge

theorem idealSupport_injective_on_squarefree
    (F : Finset (Ideal O)) {I J : Ideal O} (hI : I ∈ F) (hJ : J ∈ F)
    (hsI : Squarefree I) (hsJ : Squarefree J)
    (h : idealSupport F I = idealSupport F J) : I = J := by
  have hfac : UniqueFactorizationMonoid.normalizedFactors I =
      UniqueFactorizationMonoid.normalizedFactors J := by
    rw [Multiset.Nodup.ext
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hsI.ne_zero).mp hsI)
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hsJ.ne_zero).mp hsJ)]
    intro P
    constructor
    · intro hP
      let p : primePool F := ⟨P, mem_primePool_iff.mpr ⟨I, hI, hP⟩⟩
      have hp : p ∈ idealSupport F I := (mem_idealSupport_iff F I p).mpr hP
      rw [h] at hp
      exact (mem_idealSupport_iff F J p).mp hp
    · intro hP
      let p : primePool F := ⟨P, mem_primePool_iff.mpr ⟨J, hJ, hP⟩⟩
      have hp : p ∈ idealSupport F J := (mem_idealSupport_iff F J p).mpr hP
      rw [← h] at hp
      exact (mem_idealSupport_iff F I p).mp hp
  rw [← Ideal.prod_normalizedFactors_eq_self hsI.ne_zero,
    ← Ideal.prod_normalizedFactors_eq_self hsJ.ne_zero, hfac]

theorem baseChangeWeight_eq_zero_of_not_squarefree
    {q : ℕ} (χ : DirichletCharacter ℂ q) {I : Ideal O} (hI : ¬ Squarefree I) :
    baseChangeWeight χ I = 0 := by
  simp only [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hI,
    Int.cast_zero, zero_mul]

end ConcretePrimeRowBridge

end

end OAI

end



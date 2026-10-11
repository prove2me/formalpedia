-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0078
-- name    : PNT_ZeroFree_433_0078
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T21:26:47.800372+00:00
-- url     : https://prove2.me/theorems/512b2076-6f91-4789-a735-6d139751549b
-- title:
--   Zero-free region foundations: Fourier.FrequencyTwists [0078]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Fourier.FrequencyTwists
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Fourier/FrequencyTwists.lean#L81-L649

import Definitions.Def_PNT_ZeroFree_433_0073
import Definitions.Def_PNT_ZeroFree_433_0077

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Fourier/FrequencyTwists.lean#L81-L649
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Fourier.FrequencyTwists
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

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge

lemma logPhase_temperate (t : ℝ) : (logPhase t).HasTemperateGrowth := by
  have hl : Function.HasTemperateGrowth (fun x : ℝ => (2 * Real.pi * t) * x) := by
    simpa [Pi.smul_def, smul_eq_mul] using (((2 * Real.pi * t) • ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth)
  exact Complex.hasTemperateGrowth_exp_mul_I.comp hl

def frequencyTwist (g : 𝓢(ℝ, ℂ)) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (logPhase t) g

@[simp] lemma frequencyTwist_apply (g : 𝓢(ℝ, ℂ)) (t x : ℝ) :
    frequencyTwist g t x = logPhase t x * g x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (logPhase_temperate t) g x

lemma logPhase_add_frequency (t s x : ℝ) :
    logPhase (t + s) x = logPhase t x * logPhase s x := by
  unfold logPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] lemma frequencyTwist_twice (g : 𝓢(ℝ, ℂ)) (t s : ℝ) :
    frequencyTwist (frequencyTwist g t) s = frequencyTwist g (t + s) := by
  ext x
  simp only [frequencyTwist_apply, logPhase_add_frequency]
  ring

@[simp] lemma frequencyTwist_norm (g : 𝓢(ℝ, ℂ)) (t x : ℝ) :
    ‖frequencyTwist g t x‖ = ‖g x‖ := by simp [logPhase_norm]

lemma frequencyTwist_tsupport (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    tsupport (frequencyTwist g t) = tsupport g := by
  apply congrArg (fun s : Set ℝ => closure s)
  ext x
  have hp : logPhase t x ≠ 0 := by
    intro hz
    have hn := logPhase_norm t x
    rw [hz, norm_zero] at hn
    norm_num at hn
  simp only [Function.mem_support, frequencyTwist_apply, ne_eq, mul_eq_zero, hp, false_or]

def phaseDerivative (t : ℝ) : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I

lemma logPhase_hasDerivAt (t x : ℝ) :
    HasDerivAt (logPhase t) (phaseDerivative t * logPhase t x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (phaseDerivative t)).cexp
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] at h
  have he (y : ℝ) : Complex.exp (phaseDerivative t * (y : ℂ)) = logPhase t y := by
    unfold phaseDerivative logPhase
    congr 1
    push_cast
    ring
  simp_rw [he] at h
  simpa only [mul_comm] using h

lemma logPhase_iteratedDeriv (t : ℝ) (n : ℕ) :
    iteratedDeriv n (logPhase t) = fun x => phaseDerivative t ^ n * logPhase t x := by
  induction n with
  | zero => funext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [show deriv (fun y => phaseDerivative t ^ n * logPhase t y) x =
        phaseDerivative t ^ n * (phaseDerivative t * logPhase t x) from
      ((logPhase_hasDerivAt t x).const_mul _).deriv]
    simp only [pow_succ]
    ring

lemma phaseDerivative_norm (t : ℝ) : ‖phaseDerivative t‖ = 2 * Real.pi * ‖t‖ := by
  simp only [phaseDerivative, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
  rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), Real.norm_of_nonneg Real.pi_pos.le]

lemma logPhase_iteratedFDeriv_norm (t x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (logPhase t) x‖ = (2 * Real.pi * ‖t‖) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, logPhase_iteratedDeriv]
  simp only [norm_mul, norm_pow, phaseDerivative_norm, logPhase_norm, mul_one]

def derivativeSeminormSum (g : 𝓢(ℝ, ℂ)) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (SchwartzMap.seminorm ℝ k i) g

lemma derivativeSeminormSum_nonneg (g : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    0 ≤ derivativeSeminormSum g k n := by unfold derivativeSeminormSum; positivity

lemma seminorm_le_derivativeSeminormSum (g : 𝓢(ℝ, ℂ)) (k n i : ℕ) (hi : i ≤ n) :
    (SchwartzMap.seminorm ℝ k i) g ≤ derivativeSeminormSum g k n := by
  apply Finset.single_le_sum (s := Finset.range (n + 1))
    (f := fun j => (SchwartzMap.seminorm ℝ k j) g) (a := i)
  · intro j hj; positivity
  · exact Finset.mem_range.mpr (by omega)

theorem frequencyTwist_seminorm_bound (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (derivativeSeminormSum_nonneg _ _ _))
  intro x
  have hh := norm_iteratedFDeriv_mul_le (logPhase_temperate t).1 (g.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hfun : (frequencyTwist g t : ℝ → ℂ) = fun x => logPhase t x * g x := by
    funext x; exact frequencyTwist_apply g t x
  rw [hfun]
  calc
    _ ≤ ‖x‖^k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (logPhase t) x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (2 * Real.pi * ‖t‖)^i * (‖x‖^k * ‖iteratedFDeriv ℝ (n-i) g x‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [logPhase_iteratedFDeriv_norm]
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
      have hp : (2 * Real.pi * ‖t‖)^i ≤ (1 + 2 * Real.pi * ‖t‖)^n := by
        calc
          _ ≤ (1 + 2 * Real.pi * ‖t‖)^i := by gcongr; linarith
          _ ≤ _ := pow_le_pow_right₀ (by
            have hc : 0 ≤ 2 * Real.pi * ‖t‖ := by positivity
            linarith) hin
      have hs := (SchwartzMap.le_seminorm ℝ k (n-i) g x).trans
        (seminorm_le_derivativeSeminormSum g k n (n-i) (Nat.sub_le n i))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hs (by positivity)
        (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

theorem frequencyTwist_seminorm_polynomial (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      ((2 : ℝ)^n * (1 + 2 * Real.pi)^n * derivativeSeminormSum g k n) * (1 + ‖t‖)^n := by
  have hsum := derivativeSeminormSum_nonneg g k n
  have hp : 1 + 2 * Real.pi * ‖t‖ ≤ (1 + 2 * Real.pi) * (1 + ‖t‖) := by
    nlinarith [Real.pi_pos, norm_nonneg t]
  calc
    _ ≤ (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n :=
      frequencyTwist_seminorm_bound g t k n
    _ ≤ (2 : ℝ)^n * ((1 + 2 * Real.pi) * (1 + ‖t‖))^n * derivativeSeminormSum g k n := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

def twistSourceBound (g : 𝓢(ℝ, ℂ)) (K : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (K + 1),
    ((2 : ℝ)^i * (1 + 2 * Real.pi)^i *
      (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i))

lemma twistSourceBound_nonneg (g : 𝓢(ℝ, ℂ)) (K : ℕ) : 0 ≤ twistSourceBound g K := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (add_nonneg (derivativeSeminormSum_nonneg _ _ _) (derivativeSeminormSum_nonneg _ _ _))

theorem profileSourceBound_frequencyTwist (g : 𝓢(ℝ, ℂ)) (t : ℝ) (K : ℕ) :
    profileSourceBound (frequencyTwist g t) K ≤ twistSourceBound g K * (1 + ‖t‖)^K := by
  unfold profileSourceBound twistSourceBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ K := Finset.mem_range_succ_iff.mp hi
  have hb := add_le_add (frequencyTwist_seminorm_polynomial g t 0 i)
    (frequencyTwist_seminorm_polynomial g t (volume : Measure ℝ).integrablePower i)
  have hn : 0 ≤ (2 : ℝ)^i * (1 + 2 * Real.pi)^i *
      (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i) :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (add_nonneg (derivativeSeminormSum_nonneg _ _ _) (derivativeSeminormSum_nonneg _ _ _))
  calc
    _ ≤ ((2 : ℝ)^i * (1 + 2 * Real.pi)^i *
        (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i)) *
          (1 + ‖t‖)^i := by convert! hb using 1 ; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hin) hn

lemma fourierPointBound_mono (K : ℕ) {C D : ℝ} (hCD : C ≤ D) :
    fourierPointBound K C ≤ fourierPointBound K D := by
  unfold fourierPointBound fourierSeminormBound
  gcongr

lemma fourierPointBound_mul (K : ℕ) (C D : ℝ) :
    fourierPointBound K (C * D) = fourierPointBound K C * D := by
  unfold fourierPointBound fourierSeminormBound
  ring

theorem twisted_profile_fourier_envelope (g : 𝓢(ℝ, ℂ)) (t s : ℝ) (J : ℕ) :
    ‖(𝓕 (frequencyTwist g t)) s‖ ≤
      fourierPointBound (J + 2) (twistSourceBound g (J + 2)) *
        (1 + ‖t‖)^(J + 2) * FirstPassCubeLabels.firstLogDensity J s := by
  calc
    _ ≤ fourierPointBound (J + 2) (profileSourceBound (frequencyTwist g t) (J + 2)) *
        FirstPassCubeLabels.firstLogDensity J s := profile_fourier_envelope _ _ _
    _ ≤ fourierPointBound (J + 2) (twistSourceBound g (J + 2) * (1 + ‖t‖)^(J + 2)) *
        FirstPassCubeLabels.firstLogDensity J s :=
      mul_le_mul_of_nonneg_right (fourierPointBound_mono _ (profileSourceBound_frequencyTwist _ _ _))
        (FirstPassCubeLabels.firstLogDensity_nonneg _ _)
    _ = _ := by rw [fourierPointBound_mul]

end JointLogSeparation

section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
namespace JointLogSeparation
open FourierBridge

lemma integrable_phase_schwartz (b : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Integrable (fun t : ℝ => logPhase t x * b t) := by
  have h := FirstPassCubeLabels.integrable_log_pair b x 0 1
  convert! h using 1
  funext t
  simp [logPhase, mul_comm]

theorem finite_triple_phase_integral {α : Type*} (s : Finset α)
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (x y z : α → ℝ) (c : α → ℂ) :
    (∑ i ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      (logPhase t₁ (x i) * b₁ t₁) * ((logPhase t₂ (y i) * b₂ t₂) *
        ((logPhase t₃ (z i) * b₃ t₃) * c i))) =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∑ i ∈ s,
      (logPhase t₁ (x i) * b₁ t₁) * ((logPhase t₂ (y i) * b₂ t₂) *
        ((logPhase t₃ (z i) * b₃ t₃) * c i)) := by
  let f := fun i (t₁ t₂ t₃ : ℝ) =>
    (logPhase t₁ (x i) * b₁ t₁) * ((logPhase t₂ (y i) * b₂ t₂) *
        ((logPhase t₃ (z i) * b₃ t₃) * c i))
  have hi₃ (i : α) (t₁ t₂ : ℝ) : Integrable (f i t₁ t₂) :=
    (((integrable_phase_schwartz b₃ (z i)).mul_const (c i)).const_mul _).const_mul _
  have hi₂ (i : α) (t₁ : ℝ) : Integrable (fun t₂ => ∫ t₃ : ℝ, f i t₁ t₂ t₃) := by
    simp only [f, integral_const_mul, integral_mul_const]
    exact ((integrable_phase_schwartz b₂ (y i)).mul_const _).const_mul _
  have hi₁ (i : α) : Integrable (fun t₁ => ∫ t₂ : ℝ, ∫ t₃ : ℝ, f i t₁ t₂ t₃) := by
    simp only [f, integral_const_mul, integral_mul_const]
    exact (integrable_phase_schwartz b₁ (x i)).mul_const _
  change (∑ i ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, f i t₁ t₂ t₃) = _
  rw [← integral_finsetSum _ (fun i _ => hi₁ i)]
  apply integral_congr_ae
  filter_upwards [] with t₁
  rw [← integral_finsetSum _ (fun i _ => hi₂ i t₁)]
  apply integral_congr_ae
  filter_upwards [] with t₂
  exact (integral_finsetSum _ (fun i _ => hi₃ i t₁ t₂)).symm

end JointLogSeparation

namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog firstLogDensity)
open JointLogSeparation (outerWindow fixedColumnTest)
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def postCommonSmoothPair (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap X₁ X₂ R : ℝ) : ℂ :=
  ∑ N ∈ F.powerset, ∑ M ∈ F.powerset,
    star (secondChildColumn p hp hcop hg Ψ₁ m f y₁ (fun _ => 1) N) *
      secondChildColumn p hp hcop hg Ψ₂ m f y₂ (fun _ => 1) M *
      (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
        A₁ (z + columnLog p X₁ N) * A₂ (z + columnLog p X₂ M) *
        EisensteinSchwartzPoisson.paperRadialFourier W
          (R * Real.exp (kap - ud - 2 * ue - 2 * uv - columnLog p X₁ N - columnLog p X₂ M)))

def fixedSecondTest (V : ℝ → ℂ) (X t s : ℝ) (negative : Bool) (N : Finset ι) : ℂ :=
  if negative then star (fixedColumnTest V (t-s) (columnLog p X N))
  else fixedColumnTest V (t-s) (columnLog p X N)

theorem postCommonSmoothPair_fixed_tests
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap X₁ X₂ R : ℝ) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ a a' : ℝ,
      outerWindow V z ud ue uv kap * V 5 a * V 6 a' * A₁ (z+a) * A₂ (z+a') *
        EisensteinSchwartzPoisson.paperRadialFourier W (R * Real.exp (kap-ud-2*ue-2*uv-a-a')) =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        outerWindow V z ud ue uv kap * logPhase (t₁+t₂) z *
          logPhase t₃ (kap-ud-2*ue-2*uv) *
          fixedColumnTest (V 5) (t₁-t₃) a * fixedColumnTest (V 6) (t₂-t₃) a' *
          ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) :
    postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      (outerWindow V z ud ue uv kap * logPhase (t₁+t₂) z *
        logPhase t₃ (kap-ud-2*ue-2*uv) * ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) *
      star (fixedChildRow p hp hcop hg F Ψ₁ m
        (fixedSecondTest p (V 5) X₁ t₁ t₃ true) f y₁) *
      fixedChildRow p hp hcop hg F Ψ₂ m
        (fixedSecondTest p (V 6) X₂ t₂ t₃ false) f y₂ := by
  let B₁ := fun N => secondChildColumn p hp hcop hg Ψ₁ m f y₁ (fun _ => 1) N
  let B₂ := fun M => secondChildColumn p hp hcop hg Ψ₂ m f y₂ (fun _ => 1) M
  let q := fun (i : Finset ι × Finset ι) =>
    outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ i.1) * V 6 (columnLog p X₂ i.2) *
      star (B₁ i.1) * B₂ i.2
  let K := fun (i : Finset ι × Finset ι) (t₁ t₂ t₃ : ℝ) =>
    (logPhase t₁ (z + columnLog p X₁ i.1) * (𝓕 A₁) t₁) *
      ((logPhase t₂ (z + columnLog p X₂ i.2) * (𝓕 A₂) t₂) *
        ((logPhase t₃ (kap-ud-2*ue-2*uv-columnLog p X₁ i.1-columnLog p X₂ i.2) * b t₃) * q i))
  have hterm (N M : Finset ι) : star (B₁ N) * B₂ M *
      (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
        A₁ (z+columnLog p X₁ N) * A₂ (z+columnLog p X₂ M) *
        EisensteinSchwartzPoisson.paperRadialFourier W
          (R * Real.exp (kap-ud-2*ue-2*uv-columnLog p X₁ N-columnLog p X₂ M))) =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, K (N,M) t₁ t₂ t₃ := by
    rw [hsep]
    simp_rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t₁
    apply integral_congr_ae
    filter_upwards [] with t₂
    apply integral_congr_ae
    filter_upwards [] with t₃
    have hphase := JointLogSeparation.seven_phase_factor z ud ue uv kap
      (columnLog p X₁ N) (columnLog p X₂ M) t₁ t₂ t₃
    dsimp only [K, q]
    unfold fixedColumnTest
    calc
      _ = (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
        star (B₁ N) * B₂ M) *
        (logPhase (t₁+t₂) z * logPhase t₃ (kap-ud-2*ue-2*uv) *
          logPhase (t₁-t₃) (columnLog p X₁ N) * logPhase (t₂-t₃) (columnLog p X₂ M)) *
        ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃) := by ring
      _ = _ := by rw [← hphase]; ring
  calc
    _ = ∑ i ∈ F.powerset ×ˢ F.powerset, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, K i t₁ t₂ t₃ := by
      simp only [postCommonSmoothPair, Finset.sum_product]
      exact Finset.sum_congr rfl (fun N _ => Finset.sum_congr rfl (fun M _ => hterm N M))
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∑ i ∈ F.powerset ×ˢ F.powerset, K i t₁ t₂ t₃ :=
      JointLogSeparation.finite_triple_phase_integral _ (𝓕 A₁) (𝓕 A₂) b _ _ _ q
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t₁
      apply integral_congr_ae
      filter_upwards [] with t₂
      apply integral_congr_ae
      filter_upwards [] with t₃
      simp only [Finset.sum_product]
      have hcols : (∑ N ∈ F.powerset, ∑ M ∈ F.powerset, K (N,M) t₁ t₂ t₃) =
          (outerWindow V z ud ue uv kap * logPhase (t₁+t₂) z *
            logPhase t₃ (kap-ud-2*ue-2*uv) * ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) *
          (∑ N ∈ F.powerset, star (B₁ N) * fixedColumnTest (V 5) (t₁-t₃) (columnLog p X₁ N)) *
          (∑ M ∈ F.powerset, B₂ M * fixedColumnTest (V 6) (t₂-t₃) (columnLog p X₂ M)) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro N hN
        apply Finset.sum_congr rfl
        intro M hM
        have hphase := JointLogSeparation.seven_phase_factor z ud ue uv kap
          (columnLog p X₁ N) (columnLog p X₂ M) t₁ t₂ t₃
        dsimp only [K, q]
        unfold fixedColumnTest
        calc
          _ = (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
            star (B₁ N) * B₂ M) *
            (logPhase t₁ (z+columnLog p X₁ N) * logPhase t₂ (z+columnLog p X₂ M) *
              logPhase t₃ (kap-ud-2*ue-2*uv-columnLog p X₁ N-columnLog p X₂ M)) *
            ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃) := by ring
          _ = _ := by rw [hphase]; ring
      rw [hcols]
      have hleft : (∑ N ∈ F.powerset, star (B₁ N) *
          fixedColumnTest (V 5) (t₁-t₃) (columnLog p X₁ N)) =
          star (fixedChildRow p hp hcop hg F Ψ₁ m
            (fixedSecondTest p (V 5) X₁ t₁ t₃ true) f y₁) := by
        simp only [fixedChildRow, star_sum]
        apply Finset.sum_congr rfl
        intro N hN
        simp only [secondChildColumn, fixedSecondTest, ite_true, B₁,
          star_mul, star_star, mul_one]
        ring
      have hright : (∑ N ∈ F.powerset, B₂ N *
          fixedColumnTest (V 6) (t₂-t₃) (columnLog p X₂ N)) =
          fixedChildRow p hp hcop hg F Ψ₂ m
            (fixedSecondTest p (V 6) X₂ t₂ t₃ false) f y₂ := by
        apply Finset.sum_congr rfl
        intro N hN
        simp only [secondChildColumn, fixedSecondTest, Bool.false_eq_true, ite_false, B₂, mul_one]
      rw [hleft, hright]

def separatedPostCommon (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (A₁ A₂ b : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap X₁ X₂ : ℝ) : ℂ :=
  ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
    (outerWindow V z ud ue uv kap * logPhase (t₁+t₂) z *
      logPhase t₃ (kap-ud-2*ue-2*uv) * ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) *
    star (fixedChildRow p hp hcop hg F Ψ₁ m
      (fixedSecondTest p (V 5) X₁ t₁ t₃ true) f y₁) *
    fixedChildRow p hp hcop hg F Ψ₂ m
      (fixedSecondTest p (V 6) X₂ t₂ t₃ false) f y₂

theorem postCommonSmoothPair_uniform_fixed_tests
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ, (1+R)^A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
        C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      ∀ (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
        (z ud ue uv kap X₁ X₂ : ℝ),
        postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ W V
          z ud ue uv kap X₁ X₂ R =
        separatedPostCommon p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ b V
          z ud ue uv kap X₁ X₂ := by
  obtain ⟨C, hC, hsep⟩ := JointLogSeparation.seven_kernel_separation A₁ A₂ W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hpoint, hint⟩ := hsep R hR
  refine ⟨b, hpoint, ?_⟩
  intro F Ψ₁ Ψ₂ m f y₁ y₂ z ud ue uv kap X₁ X₂
  exact postCommonSmoothPair_fixed_tests p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ W V
    z ud ue uv kap X₁ X₂ R b (hb z ud ue uv kap)

end SecondPassArithmetic
end

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem labeled_child_second_energy_pushforward (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (negative : Bool),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
      (∑ x ∈ s, ‖w x‖ *
        ‖fixedChildRow p hp hcop hg F Ψ m H (label x)
          (if negative then -newRow x else newRow x)‖ ^ 2) ≤
      B * C * (lengthScale * Ideal.absNorm b0) ^ ε *
        ∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ m H negative u z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := second_energy_selected_family (κ := Oˣ) ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w B lengthScale label F Ψ m H negative hb0 hB hL hvalid hmap ht hnorm hw hlabel
  let sel : OldTuple → Oˣ := fun x => if hx : x ∈ s then
    Classical.choose (exists_label_unit (label x) (newLabel x) (hlabel x hx)) else 1
  have hsel (x : OldTuple) (hx : x ∈ s) : label x = (sel x : O) * idealGenerator (newLabel x) := by
    simp only [sel, dif_pos hx]
    exact Classical.choose_spec (exists_label_unit (label x) (newLabel x) (hlabel x hx))
  have hh := hb s t b0 w B lengthScale (idealChildRow p hp hcop hg F Ψ m H negative)
    sel hb0 hB hL hvalid hmap ht hnorm hw
  calc
    _ = ∑ x ∈ s, ‖w x‖ *
        ‖idealChildRow p hp hcop hg F Ψ m H negative (sel x) (newLabel x, newRow x)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hsel x hx]
      rfl
    _ ≤ _ := hh

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem support_child_label_span (x : OldTuple) (V : Finset ι)
    (hV : (∏ i ∈ V, Ideal.span {p i}) = x.v) :
    Ideal.span {idealGenerator (x.core 0) * idealGenerator (x.core 1) *
      idealGenerator (x.core 2) * ∏ i ∈ V, p i} = newLabel x := by
  simp only [newLabel, ← Ideal.span_singleton_mul_span_singleton, span_idealGenerator]
  rw [FiniteGaussPhase.span_finset_prod, hV]

end

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)
open RayFourExpansion (RayCharacter gCoeff crossCoeff)

lemma rayMonoid_norm_le_one (χ : RayCharacter) (a : O) : ‖rayMonoid χ a‖ ≤ 1 :=
  FiniteRayExpansion.norm_char_le_one χ _

lemma secondRayMinus_norm_le (Ψ : O →* ℂ) (z : SecondRayIndex) (a : O) :
    ‖secondRayMinus Ψ z a‖ ≤ ‖Ψ a‖ := by
  simp only [secondRayMinus, MonoidHom.mul_apply, norm_mul, conjugateRayMonoid_apply, norm_star]
  calc
    _ ≤ 1 * (1 * ‖Ψ a‖) := by
      gcongr <;> exact FiniteRayExpansion.norm_char_le_one _ _
    _ = _ := by ring

lemma secondRayPlus_norm_le (Ψ : O →* ℂ) (z : SecondRayIndex) (a : O) :
    ‖secondRayPlus Ψ z a‖ ≤ ‖Ψ a‖ := by
  simp only [secondRayPlus, MonoidHom.mul_apply, norm_mul, conjugateRayMonoid_apply, rayMonoid_apply, norm_star]
  calc
    _ ≤ 1 * (1 * ‖Ψ a‖) := by
      gcongr <;> exact FiniteRayExpansion.norm_char_le_one _ _
    _ = _ := by ring

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondPreColumn_norm_le
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (m c d e k : O) (S : Finset ι) :
    ‖secondPreColumn p hp hcop hg Ψ m c d e k (fun _ => 1) S‖ ≤ ‖Ψ (∏ i ∈ S, p i)‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) S m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [secondPreColumn, norm_mul, norm_pow, norm_star, norm_one,
    columnCoefficient_norm_one p hp hcop hg hc S]
  calc
    _ ≤ 1 * ‖Ψ (∏ i ∈ S, p i)‖ * 1 * 1 ^ 4 * 1 * 1 * 1 * 1 := by
      gcongr <;> first | exact hm | exact finiteSquarefreeRow_norm_le_one _ hg S _
    _ = _ := by ring

theorem secondCommonWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O) (S : Finset ι) :
    ‖secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ S‖ ≤
      ‖Ψ₁ (∏ i ∈ S, p i)‖ * ‖Ψ₂ (∏ i ∈ S, p i)‖ := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hmu : ‖supportMobius (fun i => Ideal.span {p i}) S‖ = 1 := by
    have h := congrArg norm (FirstCauchyArithmetic.supportMobius_sq _ hprime hinj S)
    simp only [norm_mul, norm_one] at h
    nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) S)]
  simp only [secondCommonWeight, norm_mul, norm_star, hmu, one_mul]
  exact mul_le_mul (secondPreColumn_norm_le p hp hcop hg hc Ψ₁ _ _ _ _ _ S)
    (secondPreColumn_norm_le p hp hcop hg hc Ψ₂ _ _ _ _ _ S) (norm_nonneg _) (norm_nonneg _)

theorem secondTotalWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O) (z : SecondRayIndex) (S : Finset ι)
    (hΨ₁ : ‖Ψ₁ (∏ i ∈ S, p i)‖ ≤ 1) (hΨ₂ : ‖Ψ₂ (∏ i ∈ S, p i)‖ ≤ 1) :
    ‖secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,S)‖ ≤ ‖secondRayCoefficient z‖ := by
  have h := secondCommonWeight_norm_le p hp hcop hg hinj hc
    (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z) m r c d e k (-k) S
  have h₁ := (secondRayMinus_norm_le Ψ₁ z (∏ i ∈ S, p i)).trans hΨ₁
  have h₂ := (secondRayPlus_norm_le Ψ₂ z (∏ i ∈ S, p i)).trans hΨ₂
  have hc' : ‖secondCommonWeight p hp hcop hg (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
      m r c d e k (-k) S‖ ≤ 1 := by
    apply h.trans
    simpa using mul_le_mul h₁ h₂ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simp only [secondTotalWeight, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hc'

end

theorem secondRayCoefficient_mass :
    (∑ z : SecondRayIndex, ‖secondRayCoefficient z‖) ≤ 512 * 32 ^ 2 := by
  have hG := RayFourExpansion.gCoeff_sum_norm_le
  have hQ := RayFourExpansion.crossCoeff_sum_norm_le
  have heq : (∑ z : SecondRayIndex, ‖secondRayCoefficient z‖) =
      (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) *
        (∑ a : RayCharacter, ‖gCoeff a‖) ^ 2 := by
    simp only [secondRayCoefficient, Fintype.sum_prod_type, norm_mul, norm_star, pow_two,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro χ hχ
    apply Finset.sum_congr rfl
    intro η hη
    ring
  rw [heq]
  exact mul_le_mul hQ (pow_le_pow_left₀ (by positivity) hG 2) (by positivity) (by norm_num)

end SecondPassArithmetic

end

end OAI

end



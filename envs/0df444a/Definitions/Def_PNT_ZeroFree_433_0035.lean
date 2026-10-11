-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0035
-- name    : PNT_ZeroFree_433_0035
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:05:45.226709+00:00
-- url     : https://prove2.me/theorems/d609db64-da5e-43f2-bdb5-eac256cfde31
-- title:
--   Zero-free region foundations: Fourier.PositiveLogProfiles [0035]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Fourier.PositiveLogProfiles
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Fourier/PositiveLogProfiles.lean#L54-L743

import Definitions.Def_PNT_ZeroFree_433_0007

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Fourier/PositiveLogProfiles.lean#L54-L743
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Fourier.PositiveLogProfiles
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
open ActualEisensteinCubic
open ActualEisensteinCubic
open Filter
open scoped Topology
open ActualEisensteinCubic
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

namespace TwoPassProfiles

theorem log_dyad_bound (r : ℝ) (hr₁ : 1 ≤ r) (hr₂ : r ≤ 2) :
    |Real.log r| ≤ Real.log 2 := by
  have hlog0 : 0 ≤ Real.log r := by
    simpa using Real.log_le_log (by positivity : (0 : ℝ) < 1) hr₁
  have hlog2 : Real.log r ≤ Real.log 2 :=
    Real.log_le_log (by linarith) hr₂
  simpa [abs_of_nonneg hlog0] using hlog2

end TwoPassProfiles

namespace ActualEisensteinCubic

theorem A3_primary_unit_eq_one (x : O) (hx : IsUnit x)
    (hprimary : lambda ^ 2 ∣ x - 1) : x = 1 := by
  let v : Oˣ := hx.unit
  have hv : (v : O) = x := hx.unit_spec
  have hvprimary : lambda ^ 2 ∣ (v : O) - 1 := by
    simpa only [hv] using hprimary
  have hunit : v = 1 ∨ v = -1 := by
    apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) v
    refine ⟨(1 : ℤ), ?_⟩
    simpa only [lambda, omega, Int.cast_one] using hvprimary
  rcases hunit with h1 | hneg
  · calc
      x = (v : O) := hv.symm
      _ = 1 := by rw [h1]; rfl
  · have heq : (v : O) - 1 = -(2 : O) := by
      rw [hneg]
      norm_num
    rw [heq] at hvprimary
    have htwo : lambda ^ 2 ∣ (2 : O) := (dvd_neg).mp hvprimary
    exact False.elim (lambda_not_dvd_two
      ((dvd_pow_self lambda (by decide)).trans htwo))

theorem A3_ramified_zero_lower_left
    (a b c d u : O) (hdet : a * d - b * c = 1)
    (hC : c - u * d = 0)
    (hAprimary : lambda ^ 2 ∣ (a - u * b) - 1)
    (hdprimary : lambda ^ 2 ∣ d - 1) :
    a - u * b = 1 ∧ d = 1 ∧ c = u := by
  have hc : c = u * d := sub_eq_zero.mp hC
  have hprod : (a - u * b) * d = 1 := by
    calc
      (a - u * b) * d = a * d - b * c := by rw [hc]; ring
      _ = 1 := hdet
  have hAunit : IsUnit (a - u * b) := IsUnit.of_mul_eq_one d hprod
  have hdunit : IsUnit d :=
    IsUnit.of_mul_eq_one (a - u * b) (by simpa only [mul_comm] using hprod)
  have hA1 := A3_primary_unit_eq_one (a - u * b) hAunit hAprimary
  have hd1 := A3_primary_unit_eq_one d hdunit hdprimary
  exact ⟨hA1, hd1, by simpa only [hd1, mul_one] using hc⟩

theorem A3_unramified_zero_lower_left
    (a b c : O) (hdet : a * 0 - b * c = 1)
    (hcprimary : lambda ^ 2 ∣ c - 1) :
    c = 1 ∧ -b = 1 := by
  have hprod : (-b) * c = 1 := by linear_combination hdet
  have hcunit : IsUnit c :=
    IsUnit.of_mul_eq_one (-b) (by simpa only [mul_comm] using hprod)
  have hc1 := A3_primary_unit_eq_one c hcunit hcprimary
  refine ⟨hc1, ?_⟩
  simpa only [hc1, mul_one] using hprod

end ActualEisensteinCubic

namespace FourierBridge

open scoped ContDiff FourierTransform SchwartzMap

theorem coupled_double_log_separation_schwartz
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F₁ F₂ : 𝓢(ℝ, ℂ))
    (a₁ a₂ M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (A₁ A₂ J₁ J₂ : ℕ) :
    ∃ (b₁ b₂ : ℝ → ℝ → ℂ) (C : ℝ), 0 ≤ C ∧
      ∀ R₁ R₂ : ℝ, 0 ≤ R₁ → 0 ≤ R₂ →
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F₁ (R₁ * Real.exp (∑ j : ι, a₁ j * y j)) *
            F₂ (R₂ * Real.exp (∑ j : ι, a₂ j * y j)) =
          ∫ t₁ : ℝ, (∫ t₂ : ℝ,
            (∏ j : ι, W j (y j)) *
              logPhase t₁ (∑ j : ι, a₁ j * y j) *
              logPhase t₂ (∑ j : ι, a₂ j * y j) *
              b₂ R₂ t₂) * b₁ R₁ t₁) ∧
        ((1 + R₁) ^ A₁ * (1 + R₂) ^ A₂) *
          ((∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ R₁ t₁‖) *
           (∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ R₂ t₂‖)) ≤ C := by
  classical
  obtain ⟨b₁, C₁, hC₁, h₁⟩ :=
    coupled_log_separation_schwartz W F₁ a₁ M hM hWwindow A₁ J₁
  obtain ⟨b₂, C₂, hC₂, h₂⟩ :=
    coupled_log_separation_schwartz W F₂ a₂ M hM hWwindow A₂ J₂
  refine ⟨b₁, b₂, C₁ * C₂, mul_nonneg hC₁ hC₂, ?_⟩
  intro R₁ R₂ hR₁ hR₂
  obtain ⟨hsep₁, hbound₁⟩ := h₁ R₁ hR₁
  obtain ⟨hsep₂, hbound₂⟩ := h₂ R₂ hR₂
  constructor
  · intro y
    let P : ℂ := ∏ j : ι, W j (y j)
    let s₁ : ℝ := ∑ j : ι, a₁ j * y j
    let s₂ : ℝ := ∑ j : ι, a₂ j * y j
    let Z₁ : ℂ := F₁ (R₁ * Real.exp s₁)
    let Z₂ : ℂ := F₂ (R₂ * Real.exp s₂)
    have hphase₁ (t : ℝ) :
        (∏ j : ι, W j (y j) * logPhase t (a₁ j * y j)) =
          P * logPhase t s₁ := by
      rw [Finset.prod_mul_distrib]
      simp only [P, s₁]
      congr 1
      simpa using (logPhase_sum (Finset.univ : Finset ι) t
        (fun j => a₁ j * y j)).symm
    have hphase₂ (t : ℝ) :
        (∏ j : ι, W j (y j) * logPhase t (a₂ j * y j)) =
          P * logPhase t s₂ := by
      rw [Finset.prod_mul_distrib]
      simp only [P, s₂]
      congr 1
      simpa using (logPhase_sum (Finset.univ : Finset ι) t
        (fun j => a₂ j * y j)).symm
    have hsep₁' : P * Z₁ =
        ∫ t₁ : ℝ, (P * logPhase t₁ s₁) * b₁ R₁ t₁ := by
      simpa only [P, Z₁, s₁, hphase₁] using hsep₁ y
    have hsep₂' : P * Z₂ =
        ∫ t₂ : ℝ, (P * logPhase t₂ s₂) * b₂ R₂ t₂ := by
      simpa only [P, Z₂, s₂, hphase₂] using hsep₂ y
    have hinner (t₁ : ℝ) :
        P * logPhase t₁ s₁ * Z₂ =
          ∫ t₂ : ℝ,
            (P * logPhase t₁ s₁ * logPhase t₂ s₂) *
              b₂ R₂ t₂ := by
      calc
        P * logPhase t₁ s₁ * Z₂ =
            logPhase t₁ s₁ * (P * Z₂) := by ring
        _ = logPhase t₁ s₁ *
            (∫ t₂ : ℝ, (P * logPhase t₂ s₂) * b₂ R₂ t₂) := by
              rw [hsep₂']
        _ = ∫ t₂ : ℝ,
            logPhase t₁ s₁ *
              ((P * logPhase t₂ s₂) * b₂ R₂ t₂) := by
                rw [integral_const_mul]
        _ = ∫ t₂ : ℝ,
            (P * logPhase t₁ s₁ * logPhase t₂ s₂) *
              b₂ R₂ t₂ := by
                apply integral_congr_ae
                filter_upwards [] with t₂
                ring
    change P * Z₁ * Z₂ = _
    calc
      P * Z₁ * Z₂ =
          (∫ t₁ : ℝ, (P * logPhase t₁ s₁) * b₁ R₁ t₁) * Z₂ := by
            rw [hsep₁']
      _ = ∫ t₁ : ℝ,
          ((P * logPhase t₁ s₁) * b₁ R₁ t₁) * Z₂ := by
            rw [integral_mul_const]
      _ = ∫ t₁ : ℝ,
          (P * logPhase t₁ s₁ * Z₂) * b₁ R₁ t₁ := by
            apply integral_congr_ae
            filter_upwards [] with t₁
            ring
      _ = ∫ t₁ : ℝ, (∫ t₂ : ℝ,
          (P * logPhase t₁ s₁ * logPhase t₂ s₂) *
            b₂ R₂ t₂) * b₁ R₁ t₁ := by
            apply integral_congr_ae
            filter_upwards [] with t₁
            rw [hinner t₁]
  · let I₁ : ℝ := ∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ R₁ t₁‖
    let I₂ : ℝ := ∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ R₂ t₂‖
    have hI₁ : 0 ≤ I₁ := by
      dsimp [I₁]
      apply integral_nonneg
      intro t
      positivity
    have hI₂ : 0 ≤ I₂ := by
      dsimp [I₂]
      apply integral_nonneg
      intro t
      positivity
    have hP₁ : 0 ≤ (1 + R₁) ^ A₁ := pow_nonneg (by linarith) _
    have hP₂ : 0 ≤ (1 + R₂) ^ A₂ := pow_nonneg (by linarith) _
    have hmul : ((1 + R₁) ^ A₁ * I₁) *
        ((1 + R₂) ^ A₂ * I₂) ≤ C₁ * C₂ := by
      exact mul_le_mul hbound₁ hbound₂
        (mul_nonneg hP₂ hI₂) hC₁
    simpa only [I₁, I₂, mul_comm, mul_left_comm, mul_assoc] using hmul

end FourierBridge

namespace InitialMeanSquareProfile

theorem dual_profile
    (H Z B F d s h v₁ v₂ : ℝ)
    (hH : H ≠ 0) (hZ : Z ≠ 0) (hB : B ≠ 0) (hF : F ≠ 0)
    (hd : d ≠ 0) (hs : s ≠ 0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    H * h / (d * ((s * v₁) * (s * v₂))) =
      ((d * h) / (Z ^ 2 / (H * B ^ 2))) /
        (((d * s) / F) ^ 2 *
          (v₁ / (Z / (B * F))) * (v₂ / (Z / (B * F)))) := by
  field_simp

end InitialMeanSquareProfile

open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap

namespace LocalLogFourier

noncomputable def eulerDeriv (F : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  iteratedDeriv j (fun t : ℝ => F (x * Real.exp t)) 0

theorem iteratedDeriv_log_eq_euler (F : ℝ → ℂ) (R s : ℝ) (j : ℕ) :
    iteratedDeriv j (fun z : ℝ => F (R * Real.exp z)) s =
      eulerDeriv F j (R * Real.exp s) := by
  let G : ℝ → ℂ := fun z => F (R * Real.exp z)
  have hshift : (fun t : ℝ => F ((R * Real.exp s) * Real.exp t)) =
      (fun t : ℝ => G (s + t)) := by
    funext t
    simp only [G, Real.exp_add, mul_assoc]
  unfold eulerDeriv
  rw [hshift]
  simpa [G] using (congrArg (fun h : ℝ → ℂ => h 0)
    (iteratedDeriv_comp_const_add j G s)).symm

theorem euler_two_regime_bound
    (F : ℝ → ℂ) (A K : ℕ) (Csmall Clarge : ℝ)
    (hCs : 0 ≤ Csmall) (hCl : 0 ≤ Clarge)
    (hsmall : ∀ i ≤ K, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖eulerDeriv F i x‖ ≤ Csmall)
    (hlarge : ∀ i ≤ K, ∀ x : ℝ, 1 ≤ x →
      x ^ A * ‖eulerDeriv F i x‖ ≤ Clarge)
    (i : ℕ) (hi : i ≤ K) (x : ℝ) (hx : 0 < x) :
    (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤
      (2 : ℝ) ^ A * (Csmall + Clarge) := by
  by_cases hsmallx : x ≤ 1
  · have hpow : (1 + x) ^ A ≤ (2 : ℝ) ^ A := by gcongr; linarith
    calc
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤
        (2 : ℝ) ^ A * ‖eulerDeriv F i x‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ A * Csmall :=
        mul_le_mul_of_nonneg_left (hsmall i hi x hx hsmallx) (by positivity)
      _ ≤ (2 : ℝ) ^ A * (Csmall + Clarge) := by gcongr; linarith
  · have hx1 : 1 ≤ x := le_of_lt (lt_of_not_ge hsmallx)
    have hpow : (1 + x) ^ A ≤ ((2 : ℝ) * x) ^ A := by
      gcongr
      linarith
    calc
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤
        ((2 : ℝ) * x) ^ A * ‖eulerDeriv F i x‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = (2 : ℝ) ^ A * (x ^ A * ‖eulerDeriv F i x‖) := by rw [mul_pow]; ring
      _ ≤ (2 : ℝ) ^ A * Clarge :=
        mul_le_mul_of_nonneg_left (hlarge i hi x hx1) (by positivity)
      _ ≤ (2 : ℝ) ^ A * (Csmall + Clarge) := by gcongr; linarith

noncomputable def positiveLogProfile
    (V F : ℝ → ℂ) (R : ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) : 𝓢(ℝ, ℂ) := by
  let arg : ℝ → ℝ := fun s => R * Real.exp s
  have harg : ContDiff ℝ ∞ arg := by
    dsimp [arg]
    fun_prop
  have hargpos : ∀ s, arg s ∈ Set.Ioi (0 : ℝ) := by
    intro s
    exact mul_pos hR (Real.exp_pos _)
  have hG : ContDiff ℝ ∞ (fun s => F (arg s)) := by
    simpa only [Function.comp_def] using hFpos.comp_contDiff harg hargpos
  have hH : ContDiff ℝ ∞ (fun s => V s * F (arg s)) := hVs.mul hG
  have hc : HasCompactSupport (fun s => V s * F (arg s)) := hVc.mul_right
  exact hc.toSchwartzMap hH

@[simp] theorem positiveLogProfile_apply
    (V F : ℝ → ℂ) (R s : ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) :
    positiveLogProfile V F R hVc hVs hFpos hR s =
      V s * F (R * Real.exp s) := rfl

theorem positive_log_separation
    (V F : ℝ → ℂ) (R s : ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) :
    V s * F (R * Real.exp s) =
      ∫ t : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ t s) * Complex.I) *
        (𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t := by
  rw [← positiveLogProfile_apply V F R s hVc hVs hFpos hR]
  exact FourierBridge.schwartz_log_inversion _ _

theorem euler_derivative_scale
    (F : ℝ → ℂ) (R s m CF : ℝ) (A i : ℕ)
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hms : m ≤ Real.exp s)
    (hF : (1 + R * Real.exp s) ^ A *
      ‖eulerDeriv F i (R * Real.exp s)‖ ≤ CF) :
    m ^ A * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ i (fun z : ℝ => F (R * Real.exp z)) s‖ ≤ CF := by
  have hscale : m * (1 + R) ≤ 1 + R * Real.exp s := by
    nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hms)]
  have hpow : (m * (1 + R)) ^ A ≤
      (1 + R * Real.exp s) ^ A := by gcongr
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_log_eq_euler]
  calc
    m ^ A * (1 + R) ^ A * ‖eulerDeriv F i (R * Real.exp s)‖ =
      (m * (1 + R)) ^ A * ‖eulerDeriv F i (R * Real.exp s)‖ := by rw [mul_pow]
    _ ≤ (1 + R * Real.exp s) ^ A *
      ‖eulerDeriv F i (R * Real.exp s)‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ CF := hF

theorem positive_log_product_derivative_bound
    (V F : ℝ → ℂ) (R m CW CF : ℝ) (A n : ℕ)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ n, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s)
    (hEuler : ∀ i ≤ n, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF)
    (s : ℝ) :
    m ^ A * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ n
        (fun z : ℝ => V z * F (R * Real.exp z)) s‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF := by
  let G : ℝ → ℂ := fun z => F (R * Real.exp z)
  have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp z) := by fun_prop
  have hG : ContDiff ℝ ∞ G := by
    dsimp [G]
    simpa only [Function.comp_def] using
      hFpos.comp_contDiff harg (by intro z; exact mul_pos hR (Real.exp_pos _))
  have hprod := norm_iteratedFDeriv_mul_le hVs hG s (n := n) (by first | simp | exact_mod_cast le_top)
  have hS : 0 ≤ m ^ A * (1 + R) ^ A := by positivity
  calc
    m ^ A * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ n (fun z : ℝ => V z * F (R * Real.exp z)) s‖ ≤
      (m ^ A * (1 + R) ^ A) *
        (∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i V s‖ *
            ‖iteratedFDeriv ℝ (n - i) G s‖) :=
      mul_le_mul_of_nonneg_left (by simpa [G] using hprod) hS
    _ = ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i V s‖ *
        ((m ^ A * (1 + R) ^ A) * ‖iteratedFDeriv ℝ (n - i) G s‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hVi : ‖iteratedFDeriv ℝ i V s‖ = 0
      · simp [hVi]
        positivity
      have hms := hwindow s ⟨i, hi', hVi⟩
      have hx : 0 < R * Real.exp s := mul_pos hR (Real.exp_pos _)
      have hGi := euler_derivative_scale F R s m CF A (n - i)
        hR hm hm1 hms (hEuler (n - i) (Nat.sub_le n i) _ hx)
      have hVi' := hVderiv i hi' s
      gcongr

theorem positive_log_uniform_seminorm
    (V F : ℝ → ℂ) (R m Lwin CW CF : ℝ) (A n k : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ n, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ n, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    m ^ A * (1 + R) ^ A *
      (SchwartzMap.seminorm ℝ k n)
        (positiveLogProfile V F R hVc hVs hFpos hR) ≤
      Lwin ^ k *
        (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF) := by
  let g := positiveLogProfile V F R hVc hVs hFpos hR
  let S := m ^ A * (1 + R) ^ A
  let C := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF
  have hS : 0 < S := by dsimp [S]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hLC : 0 ≤ Lwin ^ k * C := by positivity
  have hgeq : (g : ℝ → ℂ) =
      fun z => V z * F (R * Real.exp z) := by
    funext z
    exact positiveLogProfile_apply V F R z hVc hVs hFpos hR
  have hpoint (s : ℝ) :
      S * (|s| ^ k * ‖iteratedDeriv n g s‖) ≤ Lwin ^ k * C := by
    by_cases hactive : ∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0
    · obtain ⟨hms, habs⟩ := hwindow s hactive
      have hraw := positive_log_product_derivative_bound
        V F R m CW CF A n hVs hFpos hR hm hm1
        hCW hCF hVderiv
        (by intro z hz; exact (hwindow z hz).1)
        hEuler s
      have hnorm : S * ‖iteratedDeriv n g s‖ ≤ C := by
        rw [hgeq]
        simpa [S, C, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hraw
      calc
        S * (|s| ^ k * ‖iteratedDeriv n g s‖) =
          |s| ^ k * (S * ‖iteratedDeriv n g s‖) := by ring
        _ ≤ |s| ^ k * C :=
          mul_le_mul_of_nonneg_left hnorm (pow_nonneg (abs_nonneg _) _)
        _ ≤ Lwin ^ k * C :=
          mul_le_mul_of_nonneg_right (by gcongr) hC
    · have hzero (i : ℕ) (hi : i ≤ n) :
          ‖iteratedFDeriv ℝ i V s‖ = 0 := by
        by_contra hne
        exact hactive ⟨i, hi, hne⟩
      have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp z) := by fun_prop
      have hG : ContDiff ℝ ∞ (fun z : ℝ => F (R * Real.exp z)) := by
        simpa only [Function.comp_def] using
          hFpos.comp_contDiff harg (by intro z; exact mul_pos hR (Real.exp_pos _))
      have hprod := norm_iteratedFDeriv_mul_le hVs hG s (n := n) (by first | simp | exact_mod_cast le_top)
      have hsumzero :
          (∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i V s‖ *
              ‖iteratedFDeriv ℝ (n - i)
                (fun z : ℝ => F (R * Real.exp z)) s‖) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hzero i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
        ring
      have hnormzero : ‖iteratedDeriv n g s‖ = 0 := by
        have hzero' :
            ‖iteratedFDeriv ℝ n
              (fun z : ℝ => V z * F (R * Real.exp z)) s‖ = 0 :=
          le_antisymm (hprod.trans_eq hsumzero) (norm_nonneg _)
        rw [hgeq]
        simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hzero'
      simp [hnormzero, hLC]
  have hsemi : (SchwartzMap.seminorm ℝ k n) g ≤ Lwin ^ k * C / S := by
    apply SchwartzMap.seminorm_le_bound' ℝ k n g (div_nonneg hLC hS.le)
    intro s
    exact (le_div_iff₀ hS).mpr
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hpoint s)
  calc
    S * (SchwartzMap.seminorm ℝ k n) g ≤ S * (Lwin ^ k * C / S) :=
      mul_le_mul_of_nonneg_left hsemi hS.le
    _ = Lwin ^ k * C := by field_simp

noncomputable def derivativeConstant (n : ℕ) (CW CF : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF

noncomputable def momentConstant (K : ℕ) (Lwin CW CF : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1),
    (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
      derivativeConstant n CW CF

theorem derivativeConstant_nonneg (n : ℕ) (CW CF : ℝ)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) :
    0 ≤ derivativeConstant n CW CF := by
  unfold derivativeConstant
  positivity

theorem momentConstant_nonneg (K : ℕ) (Lwin CW CF : ℝ)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) :
    0 ≤ momentConstant K Lwin CW CF := by
  unfold momentConstant
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (by positivity)
    (derivativeConstant_nonneg n CW CF hCW hCF)

theorem momentConstant_dominates (K n : ℕ) (Lwin CW CF : ℝ)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hn : n ≤ K) :
    (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
      derivativeConstant n CW CF ≤ momentConstant K Lwin CW CF := by
  unfold momentConstant
  apply Finset.single_le_sum
    (f := fun i : ℕ =>
      (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
        derivativeConstant i CW CF)
    (a := n)
  · intro i hi
    exact mul_nonneg (by positivity)
      (derivativeConstant_nonneg i CW CF hCW hCF)
  · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn)

theorem positive_log_source_pair
    (V F : ℝ → ℂ) (R m Lwin CW CF C : ℝ) (A K n : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hn : n ≤ K)
    (hVderiv : ∀ i ≤ K, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ K, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF)
    (hCbound : ∀ j ≤ K,
      (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
        derivativeConstant j CW CF ≤ C) :
    (m ^ A * (1 + R) ^ A) *
      ((SchwartzMap.seminorm ℝ 0 n)
          (positiveLogProfile V F R hVc hVs hFpos hR) +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n)
          (positiveLogProfile V F R hVc hVs hFpos hR)) ≤ C := by
  let p := (volume : Measure ℝ).integrablePower
  let D : ℝ := derivativeConstant n CW CF
  let g := positiveLogProfile V F R hVc hVs hFpos hR
  have hVderiv_n : ∀ i ≤ n, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW := by
    intro i hi s
    exact hVderiv i (hi.trans hn) s
  have hwindow_n : ∀ s,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin := by
    intro s hs
    obtain ⟨i, hi, hnonzero⟩ := hs
    exact hwindow s ⟨i, hi.trans hn, hnonzero⟩
  have hEuler_n : ∀ i ≤ n, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF := by
    intro i hi x hx
    exact hEuler i (hi.trans hn) x hx
  have hzero := positive_log_uniform_seminorm
    V F R m Lwin CW CF A n 0 hVc hVs hFpos hR hm hm1
    hL hCW hCF hVderiv_n hwindow_n hEuler_n
  have hp := positive_log_uniform_seminorm
    V F R m Lwin CW CF A n p hVc hVs hFpos hR hm hm1
    hL hCW hCF hVderiv_n hwindow_n hEuler_n
  calc
    (m ^ A * (1 + R) ^ A) *
        ((SchwartzMap.seminorm ℝ 0 n) g +
          (SchwartzMap.seminorm ℝ p n) g) =
        (m ^ A * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ 0 n) g +
        (m ^ A * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ p n) g := by ring
    _ ≤ D + Lwin ^ p * D := by
      apply add_le_add
      · simpa [D, derivativeConstant, g] using hzero
      · simpa [D, derivativeConstant, g, p] using hp
    _ = (1 + Lwin ^ p) * D := by ring
    _ ≤ C := by simpa [D, p] using hCbound n hn

theorem positive_log_fourier_moment
    (V F : ℝ → ℂ) (R m Lwin CW CF : ℝ) (A J : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    (m ^ A * (1 + R) ^ A) *
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t‖) ≤
      (2 : ℝ) ^ J *
        (FourierBridge.coefficientMomentBound 0
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF) +
         FourierBridge.coefficientMomentBound J
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF)) := by
  let K := J + (volume : Measure ℝ).integrablePower
  let C := momentConstant K Lwin CW CF
  have hC : 0 ≤ C := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  apply FourierBridge.uniform_fourier_one_plus_moment _ J _ C (by positivity) hC
  intro n hn
  exact positive_log_source_pair V F R m Lwin CW CF C A K n
    hVc hVs hFpos hR hm hm1 hL hCW hCF
    (by simpa [K] using hn)
    (by simpa [K] using hVderiv)
    (by simpa [K] using hwindow)
    (by simpa [K] using hEuler)
    (by
      intro j hj
      simpa [C] using momentConstant_dominates K j Lwin CW CF hL hCW hCF hj)

theorem positive_log_fourier_bound
    (V F : ℝ → ℂ) (R m Lwin CW CF : ℝ) (A J : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    (1 + R) ^ A *
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t‖) ≤
      ((2 : ℝ) ^ J *
        (FourierBridge.coefficientMomentBound 0
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF) +
         FourierBridge.coefficientMomentBound J
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF))) / m ^ A := by
  have hpow : 0 < m ^ A := pow_pos hm _
  apply (le_div_iff₀ hpow).mpr
  have hbase := positive_log_fourier_moment V F R m Lwin CW CF A J
    hVc hVs hFpos hR hm hm1 hL hCW hCF hVderiv hwindow hEuler
  simpa [mul_assoc, mul_left_comm, mul_comm] using hbase

theorem coupled_positive_log_separation
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F V : ℝ → ℂ) (R : ℝ)
    (a y : ι → ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R)
    (hactive : (∏ j : ι, W j (y j)) ≠ 0 →
      V (∑ j : ι, a j * y j) = 1) :
    (∏ j : ι, W j (y j)) *
      F (R * Real.exp (∑ j : ι, a j * y j)) =
      ∫ t : ℝ,
        (∏ j : ι, W j (y j) *
          FourierBridge.logPhase t (a j * y j)) *
          (𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t := by
  classical
  let s : ℝ := ∑ j : ι, a j * y j
  let P : ℂ := ∏ j : ι, W j (y j)
  let b := 𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)
  have hsep : V s * F (R * Real.exp s) =
      ∫ t : ℝ, FourierBridge.logPhase t s * b t := by
    calc
      V s * F (R * Real.exp s) =
          ∫ t : ℝ, Complex.exp
            (↑(2 * Real.pi * inner ℝ t s) * Complex.I) * b t := by
        simpa [b] using
          (positive_log_separation V F R s hVc hVs hFpos hR)
      _ = ∫ t : ℝ, FourierBridge.logPhase t s * b t := by
        apply integral_congr_ae
        filter_upwards [] with t
        congr 1
        simp only [FourierBridge.logPhase, Real.inner_apply]
        congr 1
        push_cast
        ring
  have hcut : P * F (R * Real.exp s) =
      P * (V s * F (R * Real.exp s)) := by
    by_cases hP : P = 0
    · simp [hP]
    · rw [hactive (by simpa [P, s] using hP)]
      ring
  calc
    P * F (R * Real.exp s) = P * (V s * F (R * Real.exp s)) := hcut
    _ = P * (∫ t : ℝ, FourierBridge.logPhase t s * b t) := by rw [hsep]
    _ = ∫ t : ℝ, P * (FourierBridge.logPhase t s * b t) := by
      rw [integral_const_mul]
    _ = ∫ t : ℝ,
          (∏ j : ι, W j (y j) * FourierBridge.logPhase t (a j * y j)) * b t := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [show FourierBridge.logPhase t s =
          ∏ j : ι, FourierBridge.logPhase t (a j * y j) by
        simpa [s] using FourierBridge.logPhase_sum
          (Finset.univ : Finset ι) t (fun j => a j * y j)]
      rw [Finset.prod_mul_distrib]
      simp only [P]
      ring


end LocalLogFourier

end

end OAI

end



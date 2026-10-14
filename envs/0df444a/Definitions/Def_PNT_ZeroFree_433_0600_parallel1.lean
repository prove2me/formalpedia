-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0600_parallel1
-- name    : PNT_ZeroFree_433_0600_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:16:15.028652+00:00
-- url     : https://prove2.me/theorems/1255b6f7-e140-4446-8a8e-5efde47744a0
-- title:
--   Zero-free region foundations: Descent.DescentProfiles, Descent.ActualProfiles, Descent.DescentHeight [0600_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Descent.DescentProfiles
--   - OAI.NumberTheory.DirichletL.Descent.ActualProfiles
--   - OAI.NumberTheory.DirichletL.Descent.DescentHeight
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/DescentProfiles.lean#L10-L168
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/ActualProfiles.lean#L10-L98
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/DescentHeight.lean#L10-L73

import Definitions.Def_PNT_ZeroFree_433_0003
import Definitions.Def_PNT_ZeroFree_433_0010
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0053
import Definitions.Def_PNT_ZeroFree_433_0065
import Definitions.Def_PNT_ZeroFree_433_0077
import Definitions.Def_PNT_ZeroFree_433_0078
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0145
import Definitions.Def_PNT_ZeroFree_433_0152
import Definitions.Def_PNT_ZeroFree_433_0250_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/DescentProfiles.lean#L10-L168
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/ActualProfiles.lean#L10-L98
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Descent/DescentHeight.lean#L10-L73
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Descent.DescentProfiles
section
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

lemma schwartz_logPhase_inversion (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    g x = ∫ t : ℝ, logPhase t x * (𝓕 g) t := by
  convert! schwartz_log_inversion g x using 1
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  simp only [logPhase, Real.inner_apply]
  congr 1
  push_cast
  ring

theorem descent_profile_identity {ι : Type*} [Fintype ι]
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak : ι → ℝ)
    (R : ℝ) (b : 𝓢(ℝ, ℂ))
    (he : ∀ y : ι → ℝ,
      (∏ i, V i (y i)) * paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t : ℝ, (∏ i, V i (y i) * logPhase t (ak i * y i)) * b t) :
    ∀ y : ι → ℝ,
      (∏ i, V i (y i)) * g₁ (∑ i, a₁ i * y i) * g₂ (∑ i, a₂ i * y i) *
        paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 g₁) (𝓕 g₂) b (t₁, t₂, t₃) *
          (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
            logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i)) := by
  intro y
  let P : ℂ := ∏ i, V i (y i)
  let x₁ : ℝ := ∑ i, a₁ i * y i
  let x₂ : ℝ := ∑ i, a₂ i * y i
  let xk : ℝ := ∑ i, ak i * y i
  have hphase (t : ℝ) (a : ι → ℝ) :
      (∏ i, logPhase t (a i * y i)) = logPhase t (∑ i, a i * y i) :=
    (logPhase_sum Finset.univ t (fun i => a i * y i)).symm
  have hk' : P * paperRadialFourier W (R * Real.exp xk) =
      ∫ t : ℝ, P * logPhase t xk * b t := by
    simpa only [Finset.prod_mul_distrib, hphase, P, xk] using he y
  have hprod (t₁ t₂ t₃ : ℝ) :
      (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
        logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i)) =
      P * logPhase t₁ x₁ * logPhase t₂ x₂ * logPhase t₃ xk := by
    simp only [Finset.prod_mul_distrib, hphase, P, x₁, x₂, xk]
  simp only [hprod, tripleCoefficient]
  have hinner (t₁ t₂ : ℝ) :
      (∫ t₃ : ℝ, (𝓕 g₁) t₁ * ((𝓕 g₂) t₂ * b t₃) *
        (P * logPhase t₁ x₁ * logPhase t₂ x₂ * logPhase t₃ xk)) =
      ((𝓕 g₁) t₁ * (𝓕 g₂) t₂ * logPhase t₁ x₁ * logPhase t₂ x₂) *
        (P * paperRadialFourier W (R * Real.exp xk)) := by
    rw [hk', ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t₃
    ring
  simp_rw [hinner]
  have hmid (t₁ : ℝ) :
      (∫ t₂ : ℝ, ((𝓕 g₁) t₁ * (𝓕 g₂) t₂ * logPhase t₁ x₁ * logPhase t₂ x₂) *
        (P * paperRadialFourier W (R * Real.exp xk))) =
      (logPhase t₁ x₁ * (𝓕 g₁) t₁) * g₂ x₂ *
        (P * paperRadialFourier W (R * Real.exp xk)) := by
    rw [schwartz_logPhase_inversion g₂ x₂, ← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with t₂
    ring
  simp_rw [hmid]
  rw [integral_mul_const, integral_mul_const, ← schwartz_logPhase_inversion]
  dsimp only [P, x₁, x₂, xk]
  ring

theorem descent_profile_separation {ι : Type*} [Fintype ι]
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ y : ι → ℝ,
        (∏ i, V i (y i)) * g₁ (∑ i, a₁ i * y i) * g₂ (∑ i, a₂ i * y i) *
          paperRadialFourier W (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient (𝓕 g₁) (𝓕 g₂) b (t₁, t₂, t₃) *
            (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
              logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i))) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  obtain ⟨C, hC, hk⟩ := paperRadialFourier_log_separation_envelope W V ak M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, he, hi, hb, hp⟩ := hk R hR
  refine ⟨b, ?_, hi, hb, hp⟩
  exact descent_profile_identity g₁ g₂ W V a₁ a₂ ak R b he

theorem tripleCoefficient_weighted_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : Frequency =>
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖) := by
  have hi (b : 𝓢(ℝ, ℂ)) : Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖b t‖) := by
    have he : (𝓕 (𝓕⁻ b) : 𝓢(ℝ, ℂ)) = b := by simp
    simpa only [he] using AnalyticBridge.schwartz_fourier_one_plus_integrable (𝓕⁻ b) J
  convert! (hi b₁).mul_prod ((hi b₂).mul_prod (hi b₃)) using 1
  funext t
  simp only [tripleCoefficient, norm_mul]
  ring

theorem tripleCoefficient_weighted_integral (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ t : Frequency,
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖) =
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₁ t‖) *
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₂ t‖) *
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖b₃ t‖) := by
  have he (t : Frequency) :
      ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ t‖ =
      ((1 + ‖t.1‖)^J * ‖b₁ t.1‖) *
        (((1 + ‖t.2.1‖)^J * ‖b₂ t.2.1‖) * ((1 + ‖t.2.2‖)^J * ‖b₃ t.2.2‖)) := by
    simp only [tripleCoefficient, norm_mul]
    ring
  simp_rw [he]
  simp only [Measure.volume_eq_prod]
  rw [MeasureTheory.integral_prod_mul
    (fun t : ℝ => (1 + ‖t‖)^J * ‖b₁ t‖)
    (fun t : ℝ × ℝ => ((1 + ‖t.1‖)^J * ‖b₂ t.1‖) * ((1 + ‖t.2‖)^J * ‖b₃ t.2‖))]
  rw [MeasureTheory.integral_prod_mul
    (fun t : ℝ => (1 + ‖t‖)^J * ‖b₂ t‖) (fun t : ℝ => (1 + ‖t‖)^J * ‖b₃ t‖)]
  ring

theorem source_descent_profile_separation {ι : Type*} [Fintype ι]
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : ι → ℝ,
        (∏ i, V i (y i)) * W₁ (Real.exp (∑ i, a₁ i * y i)) *
          W₂ (Real.exp (∑ i, a₂ i * y i)) * paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient b₁ b₂ b₃ (t₁, t₂, t₃) *
            (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
              logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i))) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ≤ C := by
  let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
  let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
  obtain ⟨C, hC, hsep⟩ := descent_profile_separation g₁ g₂ Φ V a₁ a₂ ak M hM hV A J
  let I₁ := ∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 g₁) t‖
  let I₂ := ∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 g₂) t‖
  have hI₁ : 0 ≤ I₁ := integral_nonneg (fun t => by positivity)
  have hI₂ : 0 ≤ I₂ := integral_nonneg (fun t => by positivity)
  refine ⟨𝓕 g₁, 𝓕 g₂, I₁ * I₂ * C, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, heq, hi, hb, hp⟩ := hsep R hR
  refine ⟨b₃, ?_, tripleCoefficient_weighted_integrable _ _ _ J, ?_⟩
  · simpa only [g₁, g₂, CubicReflectionKernel.logSchwartz_apply] using heq
  · rw [tripleCoefficient_weighted_integral]
    have hh := mul_le_mul_of_nonneg_left hb (mul_nonneg hI₁ hI₂)
    convert! hh using 1 ; dsimp only [I₁, I₂] ; ring

end
end SevenEighths.InverseMoment

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Descent.ActualProfiles
section
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

def inverseNormWindow (V : ℝ → ℂ) (y : ℝ) : ℂ := V y / (Real.exp y : ℂ)
def inverseRootWindow (V : ℝ → ℂ) (y : ℝ) : ℂ := V y / (Real.sqrt (Real.exp y) : ℂ)

def firstRootWindows (V : Fin 9 → ℝ → ℂ) : Fin 9 → ℝ → ℂ :=
  ![V 0, V 1, V 2, inverseNormWindow (V 3), inverseRootWindow (V 4),
    inverseNormWindow (V 5), V 6, inverseRootWindow (V 7), inverseRootWindow (V 8)]

def firstLeftSlope : Fin 9 → ℝ := ![1, 0, 1, 0, 0, 1, 0, 1, 0]
def firstRightSlope : Fin 9 → ℝ := ![0, 1, 1, 0, 0, 1, 0, 0, 1]
def firstKernelSlope : Fin 9 → ℝ := ![0, 0, 0, -1, -1, -2, 1, -1, -1]

def secondRootWindows (V : Fin 6 → ℝ → ℂ) : Fin 6 → ℝ → ℂ :=
  ![V 0, inverseNormWindow (V 1), inverseNormWindow (V 2), V 3,
    inverseRootWindow (V 4), inverseRootWindow (V 5)]

def secondLeftSlope : Fin 6 → ℝ := ![1, 0, 1, 0, 1, 0]
def secondRightSlope : Fin 6 → ℝ := ![1, 0, 1, 0, 0, 1]
def secondKernelSlope : Fin 6 → ℝ := ![0, -1, -2, 1, -1, -1]

def firstPoissonProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 9 → ℝ → ℂ) (R : ℝ) (y : Fin 9 → ℝ) : ℂ :=
  (∏ i, firstRootWindows V i (y i)) *
    W₁ (Real.exp (∑ i, firstLeftSlope i * y i)) *
    W₂ (Real.exp (∑ i, firstRightSlope i * y i)) *
    paperRadialFourier Φ (R * Real.exp (∑ i, firstKernelSlope i * y i))

def secondPoissonProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (∏ i, secondRootWindows V i (y i)) *
    W₁ (Real.exp (∑ i, secondLeftSlope i * y i)) *
    W₂ (Real.exp (∑ i, secondRightSlope i * y i)) *
    paperRadialFourier Φ (R * Real.exp (∑ i, secondKernelSlope i * y i))

def profileMode {ι : Type*} [Fintype ι] (V : ι → ℝ → ℂ)
    (a₁ a₂ ak : ι → ℝ) (y : ι → ℝ) (t : Frequency) : ℂ :=
  ∏ i, V i (y i) * logPhase t.1 (a₁ i * y i) *
    logPhase t.2.1 (a₂ i * y i) * logPhase t.2.2 (ak i * y i)

theorem first_profile_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 9 → ℝ → ℂ) (M : Fin 9 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ V R y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient b₁ b₂ b₃ (t₁, t₂, t₃) *
            profileMode (firstRootWindows V) firstLeftSlope firstRightSlope firstKernelSlope y (t₁,t₂,t₃)) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ≤ C := by
  have hU : ∀ i y, firstRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hV _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  exact source_descent_profile_separation W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ
    (firstRootWindows V) firstLeftSlope firstRightSlope firstKernelSlope M hM hU A J

theorem second_profile_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 6 → ℝ, secondPoissonProfile W₁ W₂ Φ V R y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient b₁ b₂ b₃ (t₁, t₂, t₃) *
            profileMode (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope y (t₁,t₂,t₃)) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) ≤ C := by
  have hU : ∀ i y, secondRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hV _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  exact source_descent_profile_separation W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ
    (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope M hM hU A J

end
end SevenEighths.InverseMoment

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Descent.DescentHeight
section
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
noncomputable section

theorem frequencyTwist_fourier_moment (J : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ,
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 (frequencyTwist g θ)) t‖) ≤
        C * (1 + ‖θ‖)^(J + (volume : Measure ℝ).integrablePower) := by
  let K := J + (volume : Measure ℝ).integrablePower
  let D := twistSourceBound g K
  have hD : 0 ≤ D := twistSourceBound_nonneg g K
  let C := (2 : ℝ)^J * (coefficientMomentBound 0 D + coefficientMomentBound J D)
  have hC : 0 ≤ C := mul_nonneg (by positivity) (add_nonneg
    (coefficientMomentBound_nonneg 0 D hD) (coefficientMomentBound_nonneg J D hD))
  refine ⟨C, hC, ?_⟩
  intro θ
  let H := (1 + ‖θ‖)^K
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hs : ∀ i ≤ K,
      (SchwartzMap.seminorm ℝ 0 i) (frequencyTwist g θ) +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) (frequencyTwist g θ) ≤ D * H := by
    intro i hi
    exact (source_le_profileSourceBound (frequencyTwist g θ) K i hi).trans
      (profileSourceBound_frequencyTwist g θ K)
  have hh := uniform_fourier_one_plus_moment (frequencyTwist g θ) J 1 (D * H)
    (by norm_num) (mul_nonneg hD hH) (fun i hi => by simpa only [one_mul] using hs i hi)
  have hlin (j : ℕ) : coefficientMomentBound j (D * H) = coefficientMomentBound j D * H := by
    unfold coefficientMomentBound
    ring
  simpa only [one_mul, hlin, add_mul, C, H, K, mul_assoc, mul_add] using hh

theorem twisted_descent_profile_separation {ι : Type*} [Fintype ι]
    (g₁ g₂ Φ : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ θ₁ θ₂ : ℝ,
      (∀ y : ι → ℝ,
        (∏ i, V i (y i)) * frequencyTwist g₁ θ₁ (∑ i, a₁ i * y i) *
          frequencyTwist g₂ θ₂ (∑ i, a₂ i * y i) *
          paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ (t₁,t₂,t₃) *
            (∏ i, V i (y i) * logPhase t₁ (a₁ i * y i) *
              logPhase t₂ (a₂ i * y i) * logPhase t₃ (ak i * y i))) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ t‖) ≤
        C * (1 + ‖θ₁‖)^(J + (volume : Measure ℝ).integrablePower) *
          (1 + ‖θ₂‖)^(J + (volume : Measure ℝ).integrablePower) := by
  obtain ⟨Ck, hCk, hk⟩ := paperRadialFourier_log_separation_envelope Φ V ak M hM hV A J
  obtain ⟨C₁, hC₁, h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂, hC₂, h₂⟩ := frequencyTwist_fourier_moment J g₂
  refine ⟨C₁ * C₂ * Ck, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, he, hi, hb, hp⟩ := hk R hR
  refine ⟨b₃, ?_⟩
  intro θ₁ θ₂
  refine ⟨descent_profile_identity _ _ Φ V a₁ a₂ ak R b₃ he,
    tripleCoefficient_weighted_integrable _ _ _ J, ?_⟩
  rw [tripleCoefficient_weighted_integral]
  have hh := mul_le_mul (mul_le_mul (h₁ θ₁) (h₂ θ₂)
    (integral_nonneg (fun t => by positivity)) (by positivity)) hb
    (by positivity : 0 ≤ (1 + R)^A * ∫ t : ℝ, (1 + ‖t‖)^J * ‖b₃ t‖) (by positivity)
  convert! hh using 1 <;> ring

end
end SevenEighths.InverseMoment

end OAI

end



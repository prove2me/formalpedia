-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0036
-- name    : PNT_ZeroFree_433_0036
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T12:06:36.086329+00:00
-- url     : https://prove2.me/theorems/6b356bf1-37ee-4ab8-85e8-e8eabc413b74
-- title:
--   Zero-free region foundations: Fourier.PositiveLogProfiles [0036]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Fourier.PositiveLogProfiles
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Fourier/PositiveLogProfiles.lean#L745-L981

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0035

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Fourier/PositiveLogProfiles.lean#L745-L981
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


end TwoPassProfiles

namespace ActualEisensteinCubic


end ActualEisensteinCubic

namespace FourierBridge

open scoped ContDiff FourierTransform SchwartzMap


end FourierBridge

namespace InitialMeanSquareProfile


end InitialMeanSquareProfile

open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap

namespace LocalLogFourier


theorem coupled_positive_log_separation_uniform
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
      ∃ b : ℝ → ℂ,
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C := by
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
  let C : ℝ := B / m ^ A
  have hP : 0 ≤ P := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity)
      (add_nonneg
        (FourierBridge.coefficientMomentBound_nonneg 0 P hP)
        (FourierBridge.coefficientMomentBound_nonneg J P hP))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R hR
  let b : ℝ → ℂ := fun t =>
    (𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t
  refine ⟨b, ?_, ?_⟩
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 →
        V (∑ j : ι, a j * y j) = 1 :=
      FourierBridge.coupled_cutoff_active W V a y M hWwindow
        (by simpa [T] using hVone)
    simpa [b] using coupled_positive_log_separation W F V R a y
      hVc hVs hFpos hR hactive
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
    simpa [C, B, P, b, K, Lwin, m] using hbound

theorem coupled_positive_log_separation_two_regimes
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F : ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (A J : ℕ) (Csmall Clarge : ℝ)
    (hCs : 0 ≤ Csmall) (hCl : 0 ≤ Clarge)
    (hsmall : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x → x ≤ 1 →
        ‖eulerDeriv F i x‖ ≤ Csmall)
    (hlarge : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 1 ≤ x →
        x ^ A * ‖eulerDeriv F i x‖ ≤ Clarge) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : ℝ → ℂ,
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C := by
  apply coupled_positive_log_separation_uniform W F a M
    hM hWwindow hFpos A J
    ((2 : ℝ) ^ A * (Csmall + Clarge))
    (by positivity)
  intro i hi x hx
  exact euler_two_regime_bound F A
    (J + (volume : Measure ℝ).integrablePower)
    Csmall Clarge hCs hCl hsmall hlarge i hi x hx

theorem coupled_double_positive_log_separation
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F₁ F₂ : ℝ → ℂ)
    (a₁ a₂ M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hFpos₁ : ContDiffOn ℝ ∞ F₁ (Set.Ioi 0))
    (hFpos₂ : ContDiffOn ℝ ∞ F₂ (Set.Ioi 0))
    (A₁ A₂ J₁ J₂ : ℕ) (CF₁ CF₂ : ℝ)
    (hCF₁ : 0 ≤ CF₁) (hCF₂ : 0 ≤ CF₂)
    (hEuler₁ : ∀ i ≤ J₁ + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A₁ * ‖eulerDeriv F₁ i x‖ ≤ CF₁)
    (hEuler₂ : ∀ i ≤ J₂ + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A₂ * ‖eulerDeriv F₂ i x‖ ≤ CF₂) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R₁ R₂ : ℝ, 0 < R₁ → 0 < R₂ →
        ∃ (b₁ b₂ : ℝ → ℂ),
          (∀ y : ι → ℝ,
            (∏ j : ι, W j (y j)) *
              F₁ (R₁ * Real.exp (∑ j : ι, a₁ j * y j)) *
              F₂ (R₂ * Real.exp (∑ j : ι, a₂ j * y j)) =
            ∫ t₁ : ℝ, (∫ t₂ : ℝ,
              (∏ j : ι, W j (y j)) *
                FourierBridge.logPhase t₁ (∑ j : ι, a₁ j * y j) *
                FourierBridge.logPhase t₂ (∑ j : ι, a₂ j * y j) *
                b₂ t₂) * b₁ t₁) ∧
          ((1 + R₁) ^ A₁ * (1 + R₂) ^ A₂) *
            ((∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖) *
             (∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖)) ≤ C := by
  classical
  obtain ⟨C₁, hC₁, h₁⟩ :=
    coupled_positive_log_separation_uniform W F₁ a₁ M
      hM hWwindow hFpos₁ A₁ J₁ CF₁ hCF₁ hEuler₁
  obtain ⟨C₂, hC₂, h₂⟩ :=
    coupled_positive_log_separation_uniform W F₂ a₂ M
      hM hWwindow hFpos₂ A₂ J₂ CF₂ hCF₂ hEuler₂
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, ?_⟩
  intro R₁ R₂ hR₁ hR₂
  obtain ⟨b₁, hsep₁, hbound₁⟩ := h₁ R₁ hR₁
  obtain ⟨b₂, hsep₂, hbound₂⟩ := h₂ R₂ hR₂
  refine ⟨b₁, b₂, ?_, ?_⟩
  · intro y
    let P : ℂ := ∏ j : ι, W j (y j)
    let s₁ : ℝ := ∑ j : ι, a₁ j * y j
    let s₂ : ℝ := ∑ j : ι, a₂ j * y j
    let Z₁ : ℂ := F₁ (R₁ * Real.exp s₁)
    let Z₂ : ℂ := F₂ (R₂ * Real.exp s₂)
    have hphase₁ (t : ℝ) :
        (∏ j : ι, W j (y j) * FourierBridge.logPhase t (a₁ j * y j)) =
          P * FourierBridge.logPhase t s₁ := by
      rw [Finset.prod_mul_distrib]
      simp only [P, s₁]
      congr 1
      simpa using (FourierBridge.logPhase_sum (Finset.univ : Finset ι) t
        (fun j => a₁ j * y j)).symm
    have hphase₂ (t : ℝ) :
        (∏ j : ι, W j (y j) * FourierBridge.logPhase t (a₂ j * y j)) =
          P * FourierBridge.logPhase t s₂ := by
      rw [Finset.prod_mul_distrib]
      simp only [P, s₂]
      congr 1
      simpa using (FourierBridge.logPhase_sum (Finset.univ : Finset ι) t
        (fun j => a₂ j * y j)).symm
    have hsep₁' : P * Z₁ =
        ∫ t₁ : ℝ, (P * FourierBridge.logPhase t₁ s₁) * b₁ t₁ := by
      simpa only [P, Z₁, s₁, hphase₁] using hsep₁ y
    have hsep₂' : P * Z₂ =
        ∫ t₂ : ℝ, (P * FourierBridge.logPhase t₂ s₂) * b₂ t₂ := by
      simpa only [P, Z₂, s₂, hphase₂] using hsep₂ y
    have hinner (t₁ : ℝ) :
        P * FourierBridge.logPhase t₁ s₁ * Z₂ =
          ∫ t₂ : ℝ,
            (P * FourierBridge.logPhase t₁ s₁ * FourierBridge.logPhase t₂ s₂) *
              b₂ t₂ := by
      calc
        P * FourierBridge.logPhase t₁ s₁ * Z₂ =
            FourierBridge.logPhase t₁ s₁ * (P * Z₂) := by ring
        _ = FourierBridge.logPhase t₁ s₁ *
            (∫ t₂ : ℝ, (P * FourierBridge.logPhase t₂ s₂) * b₂ t₂) := by
              rw [hsep₂']
        _ = ∫ t₂ : ℝ,
            FourierBridge.logPhase t₁ s₁ *
              ((P * FourierBridge.logPhase t₂ s₂) * b₂ t₂) := by
                rw [integral_const_mul]
        _ = ∫ t₂ : ℝ,
            (P * FourierBridge.logPhase t₁ s₁ * FourierBridge.logPhase t₂ s₂) *
              b₂ t₂ := by
                apply integral_congr_ae
                filter_upwards [] with t₂
                ring
    change P * Z₁ * Z₂ = _
    calc
      P * Z₁ * Z₂ =
          (∫ t₁ : ℝ, (P * FourierBridge.logPhase t₁ s₁) * b₁ t₁) * Z₂ := by
            rw [hsep₁']
      _ = ∫ t₁ : ℝ,
          ((P * FourierBridge.logPhase t₁ s₁) * b₁ t₁) * Z₂ := by
            rw [integral_mul_const]
      _ = ∫ t₁ : ℝ,
          (P * FourierBridge.logPhase t₁ s₁ * Z₂) * b₁ t₁ := by
            apply integral_congr_ae
            filter_upwards [] with t₁
            ring
      _ = ∫ t₁ : ℝ, (∫ t₂ : ℝ,
          (P * FourierBridge.logPhase t₁ s₁ * FourierBridge.logPhase t₂ s₂) *
            b₂ t₂) * b₁ t₁ := by
            apply integral_congr_ae
            filter_upwards [] with t₁
            rw [hinner t₁]
  · let I₁ : ℝ := ∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖
    let I₂ : ℝ := ∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖
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

end LocalLogFourier

end

end OAI

end



-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
-- name    : OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T04:57:14.716506+00:00
-- url     : https://prove2.me/theorems/48a523bb-4f62-4f34-b364-ba6e8971b94f
-- title:
--   Positive Log Profiles
-- statement:
--   Definitions and structural lemmas for Positive Log Profiles, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Fourier/PositiveLogProfiles.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
set_option autoImplicit false
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
noncomputable def eulerDeriv (F : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  iteratedDeriv j (fun t : ℝ => F (x * Real.exp t)) 0
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
noncomputable def derivativeConstant (n : ℕ) (CW CF : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF
noncomputable def momentConstant (K : ℕ) (Lwin CW CF : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1),
    (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
      derivativeConstant n CW CF
end LocalLogFourier
end
end OAI



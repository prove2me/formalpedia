-- Prove2me | Definitions.Def_SourceProof_520dd8b482424f67cc040622
-- name    : SourceProof_520dd8b482424f67cc040622
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:15:35.297901+00:00
-- url     : https://prove2.me/theorems/0afbc990-ac04-440a-8cec-44205aaa2726
-- title:
--   LevyStochCalc source module: SourceProof_520dd8b482424f67cc040622
-- statement:
--   The original source theorem `LevyStochCalc.Examples.Nonvacuity.exists_solvesBSDEJ_windowZ` comes from the `NonvacuityBSDEJZ` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F000
import Definitions.Def_NonvacuityBSDEJZ_F000
import Definitions.Def_SourceProof_1da9cef3cd7392595155fa63
import Definitions.Def_SourceProof_969e6fb8eb30320c0ccbf403
import Definitions.Def_SourceProof_a157dd277ff36750db5f28f0

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A backward equation with jumps whose Brownian integrand carries positive energy

The scalar backward equation

  `Y_t = W_1 − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`. The generator vanishes, the horizon is `T = 1` and the terminal
datum is the Brownian value `W_1`, so the value process is the Brownian motion itself, the
Brownian integrand is the indicator `1_{(0, 1]}` of the horizon and the jump integrand is `0`.

## Main statements

* `exists_solvesBSDEJ_windowZ` — the equation is solved by a continuous modification of the
  Brownian motion together with the integrand pair `(1_{(0, 1]}, 0)`.
* `energy_windowZ` — the energy of `1_{(0, 1]}` on `[0, 1]` is `1`.
* `energy_eq_one_of_solvesBSDEJ` — every solution triple of the equation has Brownian integrand
  of energy `1` on `[0, 1]`.
* `exists_solvesBSDEJ_energy_ne_zero` — on a probability space carrying such a driver the
  equation has a solution triple and every solution triple has Brownian integrand of nonzero
  energy.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Delong, *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer 2013,
  §4.1.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.BSDEJ.Solves
open LevyStochCalc.Driver (LevyDriver)

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The integrands of the equation -/

section Fields

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))

end Fields

/-! ### A solution triple with the indicator integrand -/


theorem _root_.Prove2MeSourceProof.h_520dd8b482424f67cc040622 (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    ∃ Y : ℝ → Ω → ℝ,
      SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y (windowZ Ω)
          (fun _ _ _ => (0 : ℝ)) ∧
        ∀ t, Y t =ᵐ[P] fun ω => (D.W.W 0).W t ω := by
  obtain ⟨N, hsub, hNmeas, hNnull⟩ :=
    exists_measurable_superset_of_null (MeasureTheory.ae_iff.1 (D.W.W 0).continuous_paths)
  have hnotN : ∀ᵐ ω ∂P, ω ∈ Nᶜ := by
    rw [MeasureTheory.ae_iff]
    simpa using hNnull
  refine ⟨fun t => Set.indicator Nᶜ ((D.W.W 0).W t), ?_, ?_⟩
  · refine
      { Z_meas := LevyStochCalc.Examples.Nonvacuity.windowZ_meas
        Z_prog := LevyStochCalc.Examples.Nonvacuity.windowZ_prog D
        Z_vanish := LevyStochCalc.Examples.Nonvacuity.windowZ_vanish
        Z_sq := LevyStochCalc.Examples.Nonvacuity.windowZ_sq
        U_meas := LevyStochCalc.Examples.Nonvacuity.zeroU_meas
        U_prog := LevyStochCalc.Examples.Nonvacuity.zeroU_prog D
        U_vanish := fun _ _ _ _ => rfl
        U_sq := LevyStochCalc.Examples.Nonvacuity.zeroU_sq
        Y_meas := ?_
        Y_adapted := ?_
        Y_cadlag := ?_
        Y_sup := ?_
        eqn := ?_ }
    · have hfun : (Function.uncurry fun t => Set.indicator Nᶜ ((D.W.W 0).W t))
          = Set.indicator (Prod.snd ⁻¹' Nᶜ) (Function.uncurry (D.W.W 0).W) := by
        funext p
        by_cases hp : p.2 ∈ Nᶜ
        · rw [Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' Nᶜ from hp)]
          exact Set.indicator_of_mem hp _
        · rw [Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' Nᶜ from hp)]
          exact Set.indicator_of_notMem hp _
      rw [hfun]
      exact (D.W.W 0).joint_measurable.indicator (measurable_snd hNmeas.compl)
    · intro t
      have hle0 : augJoint D 0 ≤ augJoint D t := by
        rcases le_total (0 : ℝ) t with h | h
        · exact (augJoint D).mono h
        · exact D.augFiltration_le_of_nonpos h
      have hNt : MeasurableSet[augJoint D t] Nᶜ :=
        (hle0 _ (D.measurableSet_augFiltration_of_null hNmeas hNnull)).compl
      have hW : Measurable[augJoint D t] ((D.W.W 0).W t) :=
        (D.isBrownianFiltration_aug 0).measurable t
      exact (hW.indicator hNt).mono ((augJoint D).le_rightCont t) le_rfl
    · intro ω t
      by_cases hω : ω ∈ N
      · have hpt : ∀ s : ℝ, Set.indicator Nᶜ ((D.W.W 0).W s) ω = 0 :=
          fun s => Set.indicator_of_notMem (by simpa using hω) _
        simp only [hpt]
        exact ⟨tendsto_const_nhds, 0, tendsto_const_nhds⟩
      · have hcont : Continuous fun s => (D.W.W 0).W s ω := by
          by_contra hc
          exact hω (hsub hc)
        have hpt : ∀ s : ℝ, Set.indicator Nᶜ ((D.W.W 0).W s) ω = (D.W.W 0).W s ω :=
          fun s => Set.indicator_of_mem hω _
        simp only [hpt]
        exact ⟨(hcont.tendsto t).mono_left nhdsWithin_le_nhds, (D.W.W 0).W t ω,
          (hcont.tendsto t).mono_left nhdsWithin_le_nhds⟩
    · have hcongr : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) 1,
          (‖Set.indicator Nᶜ ((D.W.W 0).W t) ω‖₊ : ℝ≥0∞) ^ 2) ∂P
          = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) 1, (‖(D.W.W 0).W t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hnotN] with ω hω
        exact iSup_congr fun t => iSup_congr fun _ => by rw [Set.indicator_of_mem hω]
      have hcad : ∀ᵐ ω ∂P, ∀ t : ℝ, Filter.Tendsto (fun s => (D.W.W 0).W s ω)
          (nhdsWithin t (Set.Ioi t)) (nhds ((D.W.W 0).W t ω)) := by
        filter_upwards [(D.W.W 0).continuous_paths] with ω hω t
        exact (hω.tendsto t).mono_left nhdsWithin_le_nhds
      have hdoob := BSDEJ.SupBound.lintegral_biSup_sq_le_of_martingale (μ := P)
        (_root_.Prove2MeSourceProof.h_a157dd277ff36750db5f28f0 (D.W.W 0)) zero_le_one hcad
      rw [hcongr]
      refine lt_of_le_of_lt hdoob ?_
      rw [_root_.Prove2MeSourceProof.h_bfc6836a0f0c399780ee75a6 (D.W.W 0) zero_lt_one]
      exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
    · intro t ht
      have hI : ∀ t' : ℝ, 0 ≤ t' → ∀ᵐ ω ∂P,
          Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
              D.isBrownianFiltration_aug (LevyStochCalc.Examples.Nonvacuity.windowZ Ω) LevyStochCalc.Examples.Nonvacuity.windowZ_meas (LevyStochCalc.Examples.Nonvacuity.windowZ_prog D)
              (sq_int_global_of_vanishing LevyStochCalc.Examples.Nonvacuity.windowZ_vanish LevyStochCalc.Examples.Nonvacuity.windowZ_sq) t' ω
            = (D.W.W 0).W (min 1 t') ω - (D.W.W 0).W (min 0 t') ω := by
        intro t' ht'
        filter_upwards [_root_.Prove2MeSourceProof.h_969e6fb8eb30320c0ccbf403 (D.W.W 0) (augJoint D)
          (D.isBrownianFiltration_aug 0) (a := 0) (b := 1) le_rfl zero_lt_one
          (LevyStochCalc.Examples.Nonvacuity.windowZ_meas 0) (LevyStochCalc.Examples.Nonvacuity.windowZ_prog D 0)
          (sq_int_global_of_vanishing LevyStochCalc.Examples.Nonvacuity.windowZ_vanish LevyStochCalc.Examples.Nonvacuity.windowZ_sq 0) ht'] with ω hω
        have hsum : Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
              D.isBrownianFiltration_aug (LevyStochCalc.Examples.Nonvacuity.windowZ Ω) LevyStochCalc.Examples.Nonvacuity.windowZ_meas (LevyStochCalc.Examples.Nonvacuity.windowZ_prog D)
              (sq_int_global_of_vanishing LevyStochCalc.Examples.Nonvacuity.windowZ_vanish LevyStochCalc.Examples.Nonvacuity.windowZ_sq) t' ω
            = Brownian.Ito.stochasticIntegralBrownian (D.W.W 0) (augJoint D)
              (D.isBrownianFiltration_aug 0) (Brownian.Ito.indIoc Ω 0 1) (LevyStochCalc.Examples.Nonvacuity.windowZ_meas 0)
              (LevyStochCalc.Examples.Nonvacuity.windowZ_prog D 0) (sq_int_global_of_vanishing LevyStochCalc.Examples.Nonvacuity.windowZ_vanish LevyStochCalc.Examples.Nonvacuity.windowZ_sq 0)
              t' ω := by
          simp only [Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral,
            Fin.sum_univ_one]
          rfl
        rw [hsum]
        exact hω
      have hJ : ∀ t' : ℝ, 0 ≤ t' → ∀ᵐ ω ∂P,
          Poisson.Compensated.stochasticIntegral D.N (augJoint D) D.isPoissonFiltration_aug
              (fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ)) LevyStochCalc.Examples.Nonvacuity.zeroU_meas (LevyStochCalc.Examples.Nonvacuity.zeroU_prog D)
              (marked_sq_int_global_of_vanishing (fun _ _ _ _ => rfl) LevyStochCalc.Examples.Nonvacuity.zeroU_sq) t' ω = 0 := by
        intro t' ht'
        filter_upwards [_root_.Prove2MeSourceProof.h_1da9cef3cd7392595155fa63 D.N
          D.isPoissonFiltration_aug (fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ)) LevyStochCalc.Examples.Nonvacuity.zeroU_meas
          (LevyStochCalc.Examples.Nonvacuity.zeroU_prog D) (marked_sq_int_global_of_vanishing (fun _ _ _ _ => rfl) LevyStochCalc.Examples.Nonvacuity.zeroU_sq)
          ht' (fun _ _ _ _ => rfl)] with ω hω
        simpa using hω
      filter_upwards [hI 1 zero_le_one, hI t ht.1, hJ 1 zero_le_one, hJ t ht.1,
        (D.W.W 0).initial_zero, hnotN] with ω e1 e2 e3 e4 e5 e6
      rw [min_self, min_eq_left zero_le_one] at e1
      rw [min_eq_right ht.2, min_eq_left ht.1] at e2
      rw [Set.indicator_of_mem e6, integral_zero]
      linarith
  · intro t
    filter_upwards [hnotN] with ω hω
    exact Set.indicator_of_mem hω _
/-! ### The energy of the Brownian integrand -/

/-! ### The witness -/

end LevyStochCalc.Examples.Nonvacuity



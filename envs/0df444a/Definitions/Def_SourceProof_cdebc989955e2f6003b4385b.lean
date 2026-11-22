-- Prove2me | Definitions.Def_SourceProof_cdebc989955e2f6003b4385b
-- name    : SourceProof_cdebc989955e2f6003b4385b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:08:55.61256+00:00
-- url     : https://prove2.me/theorems/28631e87-d595-4066-9ef1-a90f8b0c874a
-- title:
--   LevyStochCalc source module: SourceProof_cdebc989955e2f6003b4385b
-- statement:
--   The original source theorem `LevyStochCalc.Examples.Nonvacuity.exists_solvesBSDEJ_expZ` comes from the `NonvacuityBSDEJExp` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F000
import Definitions.Def_LevyStochCalc_BSDEJ_SupBound_F002
import Definitions.Def_NonvacuityBSDEJExp_F001
import Definitions.Def_SourceProof_1da9cef3cd7392595155fa63
import Definitions.Def_SourceProof_a157dd277ff36750db5f28f0

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The explicit solution of a backward equation with the identity generator

The scalar backward equation

  `Y_t = W_1 + ∫_t^1 Y_s ds − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`. The generator is `f(s, y, z, u) = y`, the horizon is `T = 1` and the
terminal datum is the Brownian value `W_1`. Since `d(e^{1-t} W_t) = −e^{1-t} W_t dt + e^{1-t} dW_t`,
the value process is `Y_t = e^{1-t} W_t`, the Brownian integrand is the windowed weight
`e^{1-s} 1_{(0, 1]}(s)` and the jump integrand vanishes.

## Main statements

* `exists_solvesBSDEJ_expZ` — the equation is solved by `e^{1-t}` times a continuous modification
  of the Brownian motion, together with the integrand pair `(e^{1-s} 1_{(0, 1]}, 0)`.
* `energy_expZ` — the energy of `e^{1-s} 1_{(0, 1]}` on `[0, 1]` is `(e² − 1)/2`.
* `energy_eq_of_solvesBSDEJ` — every solution triple of the equation has Brownian integrand of
  energy `(e² − 1)/2` on `[0, 1]`.
* `exists_solvesBSDEJ_generator_id_energy_ne_zero` — on a probability space carrying such a
  driver the equation has this solution triple and every solution triple has Brownian integrand
  of nonzero energy.

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
open LevyStochCalc.Brownian.Ito (IsVectorItoVersion)

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The test function `(t, x) ↦ e^{1-t} x` -/

/-! ### The exponential weight -/

/-! ### The integrands of the equation -/

/-! ### Itô's formula for `e^{1-t} W_t` -/

section Version

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))

end Version

/-! ### The solution triple -/


theorem _root_.Prove2MeSourceProof.h_cdebc989955e2f6003b4385b (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    ∃ Y : ℝ → Ω → ℝ,
      SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y (expZ Ω)
          (fun _ _ _ => (0 : ℝ)) ∧
        ∀ t, Y t =ᵐ[P] fun ω => Real.exp (1 - t) * (D.W.W 0).W t ω := by
  obtain ⟨N, hsub, hNmeas, hNnull⟩ :=
    exists_measurable_superset_of_null (MeasureTheory.ae_iff.1 (D.W.W 0).continuous_paths)
  have hnotN : ∀ᵐ ω ∂P, ω ∈ Nᶜ := by
    rw [MeasureTheory.ae_iff]
    simpa using hNnull
  have hVcont : ∀ ω : Ω, Continuous fun t => Set.indicator Nᶜ ((D.W.W 0).W t) ω := by
    intro ω
    by_cases hω : ω ∈ N
    · have hpt : ∀ s : ℝ, Set.indicator Nᶜ ((D.W.W 0).W s) ω = 0 :=
        fun s => Set.indicator_of_notMem (by simpa using hω) _
      simp only [hpt]
      exact continuous_const
    · have hc : Continuous fun s => (D.W.W 0).W s ω := by
        by_contra hcc
        exact hω (hsub hcc)
      have hpt : ∀ s : ℝ, Set.indicator Nᶜ ((D.W.W 0).W s) ω = (D.W.W 0).W s ω :=
        fun s => Set.indicator_of_mem hω _
      simp only [hpt]
      exact hc
  have hVadapt : ∀ t : ℝ, Measurable[augJoint D t] (Set.indicator Nᶜ ((D.W.W 0).W t)) := by
    intro t
    have hle0 : augJoint D 0 ≤ augJoint D t := by
      rcases le_total (0 : ℝ) t with h | h
      · exact (augJoint D).mono h
      · exact D.augFiltration_le_of_nonpos h
    have hNt : MeasurableSet[augJoint D t] Nᶜ :=
      (hle0 _ (D.measurableSet_augFiltration_of_null hNmeas hNnull)).compl
    have hW : Measurable[augJoint D t] ((D.W.W 0).W t) :=
      (D.isBrownianFiltration_aug 0).measurable t
    exact hW.indicator hNt
  have hVae : ∀ t : ℝ, 0 ≤ t →
      (Set.indicator Nᶜ ((D.W.W 0).W t)) =ᵐ[P] (D.W.W 0).W t := by
    intro t _
    filter_upwards [hnotN] with ω hω
    exact Set.indicator_of_mem hω _
  have hVjoint : Measurable (Function.uncurry fun t => Set.indicator Nᶜ ((D.W.W 0).W t)) := by
    have hfun : (Function.uncurry fun t => Set.indicator Nᶜ ((D.W.W 0).W t))
        = Set.indicator (Prod.snd ⁻¹' Nᶜ) (Function.uncurry (D.W.W 0).W) := by
      funext p
      by_cases hp : p.2 ∈ Nᶜ
      · rw [Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' Nᶜ from hp)]
        exact Set.indicator_of_mem hp _
      · rw [Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' Nᶜ from hp)]
        exact Set.indicator_of_notMem hp _
    rw [hfun]
    exact (D.W.W 0).joint_measurable.indicator (measurable_snd hNmeas.compl)
  have hYcont : ∀ ω : Ω,
      Continuous fun t => Real.exp (1 - t) * Set.indicator Nᶜ ((D.W.W 0).W t) ω :=
    fun ω => (Real.continuous_exp.comp (continuous_const.sub continuous_id)).mul (hVcont ω)
  refine ⟨fun t ω => Real.exp (1 - t) * Set.indicator Nᶜ ((D.W.W 0).W t) ω, ?_, ?_⟩
  · refine
      { Z_meas := LevyStochCalc.Examples.Nonvacuity.expZ_meas
        Z_prog := LevyStochCalc.Examples.Nonvacuity.expZ_prog (augJoint D)
        Z_vanish := LevyStochCalc.Examples.Nonvacuity.expZ_vanish
        Z_sq := LevyStochCalc.Examples.Nonvacuity.expZ_sq
        U_meas := LevyStochCalc.Examples.Nonvacuity.zeroJump_meas
        U_prog := LevyStochCalc.Examples.Nonvacuity.zeroJump_prog D
        U_vanish := fun _ _ _ _ => rfl
        U_sq := LevyStochCalc.Examples.Nonvacuity.zeroJump_sq
        Y_meas := ?_
        Y_adapted := ?_
        Y_cadlag := ?_
        Y_sup := ?_
        eqn := ?_ }
    · exact ((Real.continuous_exp.measurable.comp
        (measurable_const.sub measurable_id)).comp measurable_fst).mul hVjoint
    · intro t
      exact ((hVadapt t).const_mul (Real.exp (1 - t))).mono
        ((augJoint D).le_rightCont t) le_rfl
    · intro ω t
      exact ⟨((hYcont ω).tendsto t).mono_left nhdsWithin_le_nhds,
        Real.exp (1 - t) * Set.indicator Nᶜ ((D.W.W 0).W t) ω,
        ((hYcont ω).tendsto t).mono_left nhdsWithin_le_nhds⟩
    · have hbound : ∀ ω : Ω, (⨆ r ∈ Set.Icc (0 : ℝ) 1,
          (‖Real.exp (1 - r) * Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2)
          ≤ ⨆ r ∈ Set.Icc (0 : ℝ) 1,
            (‖Real.exp 1 * Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2 := by
        intro ω
        refine iSup₂_le fun r hr => ?_
        refine le_trans (pow_le_pow_left' ?_ 2)
          (le_iSup₂ (f := fun r (_ : r ∈ Set.Icc (0 : ℝ) 1) =>
            (‖Real.exp 1 * Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2) r hr)
        refine ENNReal.coe_le_coe.mpr ?_
        rw [← NNReal.coe_le_coe]
        simp only [coe_nnnorm, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hr.1]))
          (abs_nonneg _)
      have hcongr : ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) 1,
          (‖Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2) ∂P
          = ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) 1, (‖(D.W.W 0).W r ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hnotN] with ω hω
        exact iSup_congr fun r => iSup_congr fun _ => by rw [Set.indicator_of_mem hω]
      have hcad : ∀ᵐ ω ∂P, ∀ r : ℝ, Filter.Tendsto (fun s => (D.W.W 0).W s ω)
          (nhdsWithin r (Set.Ioi r)) (nhds ((D.W.W 0).W r ω)) := by
        filter_upwards [(D.W.W 0).continuous_paths] with ω hω r
        exact (hω.tendsto r).mono_left nhdsWithin_le_nhds
      have hdoob := BSDEJ.SupBound.lintegral_biSup_sq_le_of_martingale (μ := P)
        (_root_.Prove2MeSourceProof.h_a157dd277ff36750db5f28f0 (D.W.W 0)) zero_le_one hcad
      have hfin : ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) 1,
          (‖Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
        rw [hcongr]
        refine lt_of_le_of_lt hdoob ?_
        rw [_root_.Prove2MeSourceProof.h_bfc6836a0f0c399780ee75a6 (D.W.W 0) zero_lt_one]
        exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
      calc ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) 1,
            (‖Real.exp (1 - r) * Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2) ∂P
          ≤ ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) 1,
              (‖Real.exp 1 * Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2) ∂P :=
            lintegral_mono hbound
        _ = (‖Real.exp 1‖₊ : ℝ≥0∞) ^ 2 * ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) 1,
              (‖Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2) ∂P :=
            BSDEJ.SupBound.lintegral_biSup_sq_const_mul (Real.exp 1)
              (fun r => Set.indicator Nᶜ ((D.W.W 0).W r)) 1
        _ < ⊤ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hfin
    · intro t ht
      have hJ : ∀ t' : ℝ, 0 ≤ t' → ∀ᵐ ω ∂P,
          Poisson.Compensated.stochasticIntegral D.N (augJoint D) D.isPoissonFiltration_aug
              (fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ)) LevyStochCalc.Examples.Nonvacuity.zeroJump_meas (LevyStochCalc.Examples.Nonvacuity.zeroJump_prog D)
              (marked_sq_int_global_of_vanishing (fun _ _ _ _ => rfl) LevyStochCalc.Examples.Nonvacuity.zeroJump_sq) t' ω
            = 0 := by
        intro t' ht'
        filter_upwards [_root_.Prove2MeSourceProof.h_1da9cef3cd7392595155fa63 D.N
          D.isPoissonFiltration_aug (fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ)) LevyStochCalc.Examples.Nonvacuity.zeroJump_meas
          (LevyStochCalc.Examples.Nonvacuity.zeroJump_prog D) (marked_sq_int_global_of_vanishing (fun _ _ _ _ => rfl) LevyStochCalc.Examples.Nonvacuity.zeroJump_sq)
          ht' (fun _ _ _ _ => rfl)] with ω hω
        simpa using hω
      have hsplit : ∀ ω : Ω,
          (∫ s in Set.Icc t 1, Real.exp (1 - s) * Set.indicator Nᶜ ((D.W.W 0).W s) ω)
            = (∫ s in Set.Ioc (0 : ℝ) 1,
                Real.exp (1 - s) * Set.indicator Nᶜ ((D.W.W 0).W s) ω)
              - ∫ s in Set.Ioc (0 : ℝ) t,
                  Real.exp (1 - s) * Set.indicator Nᶜ ((D.W.W 0).W s) ω := by
        intro ω
        have hdisj : Disjoint (Set.Ioc (0 : ℝ) t) (Set.Ioc t 1) :=
          Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'.1)
        have hun := setIntegral_union (μ := volume) hdisj measurableSet_Ioc
          ((hYcont ω).integrableOn_Ioc) ((hYcont ω).integrableOn_Ioc)
        rw [Set.Ioc_union_Ioc_eq_Ioc ht.1 ht.2] at hun
        rw [integral_Icc_eq_integral_Ioc, hun]
        ring
      filter_upwards [LevyStochCalc.Examples.Nonvacuity.expIto_identity_of_mem D hVcont hVadapt hVae ht,
        LevyStochCalc.Examples.Nonvacuity.expIto_identity_of_mem D hVcont hVadapt hVae (Set.right_mem_Icc.mpr zero_le_one),
        hJ 1 zero_le_one, hJ t ht.1, hVae 1 zero_le_one] with ω e1 e2 e3 e4 e5
      rw [e3, e4, hsplit ω, ← e5]
      norm_num at e2
      linarith [e1, e2]
  · intro t
    filter_upwards [hnotN] with ω hω
    rw [Set.indicator_of_mem hω]
/-! ### The energy of the Brownian integrand -/

/-! ### The witness -/

end LevyStochCalc.Examples.Nonvacuity



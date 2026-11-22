-- Prove2me | Definitions.Def_NonvacuityPRP_F000
-- name    : NonvacuityPRP_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:48:56.764113+00:00
-- url     : https://prove2.me/theorems/75ee6c84-d6c6-426e-a918-67f50abb6e67
-- title:
--   Source declarations: NonvacuityPRP
-- statement:
--   Source-preserving extracted declarations from NonvacuityPRP. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPMultidimRange_F000
import Definitions.Def_LevyStochCalc_Driver_JointFiltration_F000
import Definitions.Def_LevyStochCalc_Driver_JointRange_F000
import Definitions.Def_LevyStochCalc_Driver_PredictableRepresentation_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F001
import Definitions.Def_LevyStochCalc_Probability_MarkedPredictable_F000
import Definitions.Def_LevyStochCalc_Probability_Predictable_F000
import Definitions.Def_NonvacuityBSDEJ_F000
import Definitions.Def_NonvacuityContract_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The predictable representation of a Brownian value over a Lévy driver

The value at time `1` of the single Brownian coordinate of a Lévy driver with unit mark
intensity `δ_1` is square integrable, measurable for the augmented joint filtration at time `1`
and centred, hence a joint integral of a predictable Itô integrand and a predictable marked
integrand over the horizon `[0, 1]`. Such a representation differs from the zero one: it has
second moment `1`, and the energy of its Itô integrand or the marked energy of its compensated
integrand is nonzero.

## Main statements

* `integral_brownian_value_one_eq_zero` — a Brownian motion has mean `0` at time `1`.
* `itoIntegral_ae_zero_of_energy_eq_zero` and
  `compensatedIntegral_ae_zero_of_markedEnergy_eq_zero` — an admissible integrand of zero
  energy has an almost surely vanishing stochastic integral.
* `exists_predictable_jointIntegral_brownian_one` — the Brownian value `W_1` is a joint
  integral of predictable integrands over the augmented joint filtration.
* `lintegral_sq_jointIntegral_brownian_one` and `jointIntegral_brownian_one_not_ae_zero` —
  a joint integral representing `W_1` has second moment `1` and is not almost surely `0`.
* `energy_or_markedEnergy_ne_zero_of_brownian_one` — the Itô integrand of such a
  representation has nonzero energy, or its marked integrand has nonzero marked energy.
* `exists_predictable_representation_brownian_one` — the same statements on a probability
  space carrying a Lévy driver with one Brownian coordinate and unit mark intensity.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §5.3.
* Delong, *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer 2013,
  §3.1.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.Driver (LevyDriver)
open LevyStochCalc.Brownian.Ito (HorizonIntegrand energy)
open LevyStochCalc.Poisson.Compensated (MarkedHorizonIntegrand markedEnergy)
open LevyStochCalc.Probability (Predictable MarkedPredictable)

universe u v w

section Vanishing

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- An admissible Itô integrand of zero energy has an almost surely vanishing integral. -/
theorem itoIntegral_ae_zero_of_energy_eq_zero {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (W : Brownian.BrownianMotion P) (hℱ : Brownian.IsBrownianFiltration W ℱ) (hT : 0 < T)
    (G : HorizonIntegrand P ℱ T) (hG : energy P T G.toFun = 0) :
    G.integral W hℱ =ᵐ[P] 0 := by
  have hiso := _root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ G.toFun
    G.measurable_uncurry G.progressive G.sq_int_global hT
  have hzero : ∫⁻ ω, (‖G.integral W hℱ ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := hiso.trans hG
  have hae : AEMeasurable (fun ω => (‖G.integral W hℱ ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (((HorizonIntegrand.memLp W hℱ G).aestronglyMeasurable.aemeasurable).nnnorm
      ).coe_nnreal_ennreal.pow_const 2
  filter_upwards [(lintegral_eq_zero_iff' hae).mp hzero] with ω hω
  have h2 : (‖G.integral W hℱ ω‖₊ : ℝ≥0∞) ^ 2 = 0 := hω
  have h3 : (‖G.integral W hℱ ω‖₊ : ℝ≥0∞) = 0 :=
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
  simpa using h3
variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

/-- An admissible marked integrand of zero marked energy has an almost surely vanishing
compensated integral. -/
theorem compensatedIntegral_ae_zero_of_markedEnergy_eq_zero
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
    (N : Poisson.PoissonRandomMeasure.{u, v, w} P ν) (hℱ : Poisson.IsPoissonFiltration N ℱ)
    (hT : 0 < T) (K : MarkedHorizonIntegrand P ν ℱ T)
    (hK : markedEnergy P ν T K.toFun = 0) :
    K.integral N hℱ =ᵐ[P] 0 := by
  have hiso := Poisson.Compensated.isometry_stochasticIntegral N ℱ hℱ K.toFun
    K.measurable_uncurry K.progressive K.sq_int_global T hT
  have hzero : ∫⁻ ω, (‖K.integral N hℱ ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := hiso.trans hK
  have hae : AEMeasurable (fun ω => (‖K.integral N hℱ ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (((MarkedHorizonIntegrand.memLp N hℱ K).aestronglyMeasurable.aemeasurable).nnnorm
      ).coe_nnreal_ennreal.pow_const 2
  filter_upwards [(lintegral_eq_zero_iff' hae).mp hzero] with ω hω
  have h2 : (‖K.integral N hℱ ω‖₊ : ℝ≥0∞) ^ 2 = 0 := hω
  have h3 : (‖K.integral N hℱ ω‖₊ : ℝ≥0∞) = 0 :=
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
  simpa using h3
end Vanishing

section Terminal

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A Brownian motion has mean `0` at time `1`. -/
theorem integral_brownian_value_one_eq_zero (W : Brownian.BrownianMotion P) :
    ∫ ω, W.W 1 ω ∂P = 0 := by
  have h := Brownian.Ito.integral_increment_pow_odd W (le_refl (0 : ℝ)) one_pos
    (m := 1) odd_one
  simp only [pow_one] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [W.initial_zero] with ω hω
  rw [hω, sub_zero]
end Terminal

section Representation

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The value at time `1` of the Brownian coordinate of a Lévy driver with one Brownian
coordinate and unit mark intensity is the joint integral of a predictable Itô integrand and a
predictable marked integrand over the horizon `[0, 1]`. -/
theorem exists_predictable_jointIntegral_brownian_one (D : LevyDriver P 1 markIntensity) :
    ∃ (G : ∀ _ : Fin 1, HorizonIntegrand P (Brownian.augFiltration D.filtration P) 1)
      (K : MarkedHorizonIntegrand P markIntensity
        (Brownian.augFiltration D.filtration P) 1),
      (∀ i, Predictable (Brownian.augFiltration D.filtration P) (G i).toFun) ∧
        MarkedPredictable (Brownian.augFiltration D.filtration P) markIntensity K.toFun ∧
        (fun ω => (D.W.W 0).W 1 ω) =ᵐ[P]
          LevyDriver.jointIntegral (fun k => D.isBrownianFiltration_aug k)
            D.isPoissonFiltration_aug G K :=
  LevyDriver.exists_predictable_jointIntegral D one_pos (memLp_brownian_one D.W)
    (aestronglyMeasurable_brownian_one_augJoint D)
    (integral_brownian_value_one_eq_zero (D.W.W 0))
variable (D : LevyDriver P 1 markIntensity)
  {G : ∀ _ : Fin 1, HorizonIntegrand P (Brownian.augFiltration D.filtration P) 1}
  {K : MarkedHorizonIntegrand P markIntensity (Brownian.augFiltration D.filtration P) 1}

/-- The joint integral of a one-coordinate family and a marked integrand splits into the Itô
integral of the single coordinate and the compensated integral of the marked integrand. -/
theorem jointIntegral_fin_one_apply (ω : Ω) :
    LevyDriver.jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K ω
      = (G 0).integral (D.W.W 0) (D.isBrownianFiltration_aug 0) ω
        + K.integral D.N D.isPoissonFiltration_aug ω := by
  simp [LevyDriver.jointIntegral, Brownian.Multidim.MultidimBrownianMotion.vectorIntegral]
/-- A joint integral representing the Brownian value at time `1` has second moment `1`. -/
theorem lintegral_sq_jointIntegral_brownian_one
    (hrep : (fun ω => (D.W.W 0).W 1 ω) =ᵐ[P]
      LevyDriver.jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K) :
    ∫⁻ ω, (‖LevyDriver.jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 := by
  have hae : (fun ω => (‖LevyDriver.jointIntegral (fun k => D.isBrownianFiltration_aug k)
      D.isPoissonFiltration_aug G K ω‖₊ : ℝ≥0∞) ^ 2)
      =ᵐ[P] fun ω => (‖(D.W.W 0).W 1 ω‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [hrep] with ω hω
    rw [hω]
  rw [lintegral_congr_ae hae, _root_.Prove2MeSourceProof.h_bfc6836a0f0c399780ee75a6 (D.W.W 0) one_pos,
    ENNReal.ofReal_one]
/-- A joint integral representing the Brownian value at time `1` is not almost surely `0`. -/
theorem jointIntegral_brownian_one_not_ae_zero
    (hrep : (fun ω => (D.W.W 0).W 1 ω) =ᵐ[P]
      LevyDriver.jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K) :
    ¬ (LevyDriver.jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K =ᵐ[P] 0) := by
  intro hzero
  refine brownian_not_ae_zero (D.W.W 0) one_pos ?_
  filter_upwards [hrep, hzero] with ω h1 h2
  rw [h1, h2]
  rfl
/-- In a joint integral representing the Brownian value at time `1` the Itô integrand has
nonzero energy or the marked integrand has nonzero marked energy. -/
theorem energy_or_markedEnergy_ne_zero_of_brownian_one
    (hrep : (fun ω => (D.W.W 0).W 1 ω) =ᵐ[P]
      LevyDriver.jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K) :
    energy P 1 (G 0).toFun ≠ 0 ∨ markedEnergy P markIntensity 1 K.toFun ≠ 0 := by
  by_cases hG : energy P 1 (G 0).toFun = 0
  · by_cases hK : markedEnergy P markIntensity 1 K.toFun = 0
    · refine absurd ?_ (jointIntegral_brownian_one_not_ae_zero D hrep)
      have hG0 : (G 0).integral (D.W.W 0) (D.isBrownianFiltration_aug 0) =ᵐ[P] 0 :=
        itoIntegral_ae_zero_of_energy_eq_zero (D.W.W 0) (D.isBrownianFiltration_aug 0)
          one_pos (G 0) hG
      have hK0 : K.integral D.N D.isPoissonFiltration_aug =ᵐ[P] 0 :=
        compensatedIntegral_ae_zero_of_markedEnergy_eq_zero D.N D.isPoissonFiltration_aug
          one_pos K hK
      filter_upwards [hG0, hK0] with ω e1 e2
      rw [jointIntegral_fin_one_apply D ω]
      simp [e1, e2]
    · exact Or.inr hK
  · exact Or.inl hG
end Representation

section Capstone

/-- Some probability space carries a Lévy driver with one Brownian coordinate and unit mark
intensity together with a predictable Itô integrand and a predictable marked integrand over
the horizon `[0, 1]` whose joint integral is the Brownian value at time `1`; that joint
integral is not almost surely `0`, has second moment `1`, and one of the two energies of the
representing pair is nonzero. -/
theorem exists_predictable_representation_brownian_one :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 markIntensity)
      (G : ∀ _ : Fin 1, HorizonIntegrand P (Brownian.augFiltration D.filtration P) 1)
      (K : MarkedHorizonIntegrand P markIntensity
        (Brownian.augFiltration D.filtration P) 1),
      (∀ i, Predictable (Brownian.augFiltration D.filtration P) (G i).toFun) ∧
        MarkedPredictable (Brownian.augFiltration D.filtration P) markIntensity K.toFun ∧
        (fun ω => (D.W.W 0).W 1 ω) =ᵐ[P]
          LevyDriver.jointIntegral (fun k => D.isBrownianFiltration_aug k)
            D.isPoissonFiltration_aug G K ∧
        ¬ (LevyDriver.jointIntegral (fun k => D.isBrownianFiltration_aug k)
            D.isPoissonFiltration_aug G K =ᵐ[P] 0) ∧
        ∫⁻ ω, (‖LevyDriver.jointIntegral (fun k => D.isBrownianFiltration_aug k)
            D.isPoissonFiltration_aug G K ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 ∧
        (energy P 1 (G 0).toFun ≠ 0 ∨ markedEnergy P markIntensity 1 K.toFun ≠ 0) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := Driver.LevyDriver.exists 1 ℝ markIntensity
  obtain ⟨G, K, hGpred, hKpred, hrep⟩ := exists_predictable_jointIntegral_brownian_one D
  exact ⟨Ω, inferInstance, P, inferInstance, D, G, K, hGpred, hKpred, hrep,
    jointIntegral_brownian_one_not_ae_zero D hrep,
    lintegral_sq_jointIntegral_brownian_one D hrep,
    energy_or_markedEnergy_ne_zero_of_brownian_one D hrep⟩
end Capstone

end LevyStochCalc.Examples.Nonvacuity



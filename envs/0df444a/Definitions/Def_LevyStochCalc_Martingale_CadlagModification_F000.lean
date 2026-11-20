-- Prove2me | Definitions.Def_LevyStochCalc_Martingale_CadlagModification_F000
-- name    : LevyStochCalc_Martingale_CadlagModification_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:34:43.955729+00:00
-- url     : https://prove2.me/theorems/a7d71843-4186-4ae2-b100-b8317a42c30f
-- title:
--   Source declarations: LevyStochCalc.Martingale.CadlagModification
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Martingale.CadlagModification. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Martingale_F000
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F001
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F003
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F004

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Càdlàg modifications of real martingales

A real martingale on a right-continuous filtration whose time slices are right-continuous
in measure admits an adapted modification whose paths are almost surely càdlàg. The
modification is the right-limit regularisation along a countable dense set of times
(`ProbabilityTheory.rightContModif`), available for real quasimartingales; a martingale is
a quasimartingale because the elementary integral of a predictable indicator against it has
zero mean.

Two index sets are treated: `ℝ≥0`, where the quasimartingale theory lives (it needs a least
time), and `ℝ`, by restricting to nonnegative times and extending by zero to negative times.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LevyStochCalc.Martingale

section Modification

variable {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ}
  {μ : Measure Ω} {X Y : ι → Ω → ℝ}

/-- A strongly adapted modification of a martingale is a martingale. -/
lemma martingale_of_ae_eq (hX : Martingale X ℱ μ) (hY : StronglyAdapted ℱ Y)
    (h : ∀ t, Y t =ᵐ[μ] X t) : Martingale Y ℱ μ :=
  ⟨hY, fun s t hst => (condExp_congr_ae (h t)).trans ((hX.condExp_ae_eq hst).trans (h s).symm)⟩
end Modification

section Quasimartingale

variable {ι Ω : Type*} [LinearOrder ι] {mΩ : MeasurableSpace Ω}
  {𝓕 : Filtration ι mΩ} {μ : Measure Ω} {X : ι → Ω → ℝ}

/-- The increment of a martingale over `(min a t, min b t]` has zero integral over any
`𝓕 a`-measurable set. -/
lemma setIntegral_increment_eq_zero [IsFiniteMeasure μ] (hX : Martingale X 𝓕 μ)
    {s : Set Ω} {a b : ι} (hab : a ≤ b) (hs : MeasurableSet[𝓕 a] s) (t : ι) :
    ∫ ω in s, (X (min b t) ω - X (min a t) ω) ∂μ = 0 := by
  rcases le_or_gt a t with hat | hta
  · rw [min_eq_left hat,
      integral_sub (hX.integrable _).integrableOn (hX.integrable _).integrableOn,
      ← hX.setIntegral_eq (le_min hab hat) hs, sub_self]
  · simp [min_eq_right (hta.le.trans hab), min_eq_right hta.le]
variable [OrderBot ι]

/-- A process stopped at a constant time `t`, evaluated at time `q`, is the process at
`min q t`. -/
lemma stoppedProcess_const_apply (X : ι → Ω → ℝ) (t q : ι) (ω : Ω) :
    stoppedProcess X (fun _ => (t : WithTop ι)) q ω = X (min q t) ω := by
  rcases le_total q t with h | h
  · rw [stoppedProcess_eq_of_le (τ := fun _ => (t : WithTop ι)) (i := q) (ω := ω)
      (WithTop.coe_le_coe.2 h), min_eq_left h]
  · rw [stoppedProcess_eq_of_ge (τ := fun _ => (t : WithTop ι)) (i := q) (ω := ω)
      (WithTop.coe_le_coe.2 h), min_eq_right h]
    rfl
/-- The elementary integral of the indicator of an elementary predictable set against a
martingale has zero mean. -/
lemma integral_indicator_integral_eq_zero [IsFiniteMeasure μ] (hX : Martingale X 𝓕 μ)
    (S : ElementaryPredictableSet 𝓕) (t : ι) :
    μ[(S.indicator (1 : ℝ)).integral (ContinuousLinearMap.mul ℝ ℝ) X t] = 0 := by
  have hfun : ∀ ω, (S.indicator (1 : ℝ)).integral (ContinuousLinearMap.mul ℝ ℝ) X t ω
      = ∑ p ∈ S.I, (S.set p).indicator (fun ω => X (min p.2 t) ω - X (min p.1 t) ω) ω := by
    intro ω
    rw [ElementaryPredictableSet.integral_indicator_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [ContinuousLinearMap.mul_apply', one_mul, stoppedProcess_const_apply]
  have hint : ∀ p ∈ S.I, Integrable
      (fun ω => (S.set p).indicator (fun ω => X (min p.2 t) ω - X (min p.1 t) ω) ω) μ :=
    fun p hp => ((hX.integrable _).sub (hX.integrable _)).indicator
      (𝓕.le _ _ (S.measurableSet_set p hp))
  calc μ[(S.indicator (1 : ℝ)).integral (ContinuousLinearMap.mul ℝ ℝ) X t]
      = ∫ ω, ∑ p ∈ S.I,
          (S.set p).indicator (fun ω => X (min p.2 t) ω - X (min p.1 t) ω) ω ∂μ :=
        integral_congr_ae (Eventually.of_forall hfun)
    _ = ∑ p ∈ S.I, ∫ ω,
          (S.set p).indicator (fun ω => X (min p.2 t) ω - X (min p.1 t) ω) ω ∂μ :=
        integral_finsetSum _ hint
    _ = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        rw [integral_indicator (𝓕.le _ _ (S.measurableSet_set p hp))]
        exact setIntegral_increment_eq_zero hX (S.le_of_mem_I p hp)
          (S.measurableSet_set p hp) t
/-- A real martingale is a real quasimartingale. -/
lemma isRealQuasimartingale [IsFiniteMeasure μ]
    (hX : Martingale X 𝓕 μ) : IsRealQuasimartingale 𝓕 X μ where
  adapted := hX.stronglyAdapted.adapted
  integrable := hX.integrable
  boundedVariation t := ⟨0, fun S => (integral_indicator_integral_eq_zero hX S t).le⟩
end Quasimartingale

section NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

/-- A real martingale on a right-continuous filtration indexed by `ℝ≥0`, right-continuous in
measure at every time, has an adapted modification whose paths are almost surely càdlàg. -/
theorem exists_adapted_ae_isCadlag_nnreal [𝓕.IsRightContinuous] (hX : Martingale X 𝓕 μ)
    (hrc : ∀ t, TendstoInMeasure μ X (𝓝[>] t) (X t)) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Adapted 𝓕 Y ∧ (∀ t, Y t =ᵐ[μ] X t) ∧
      ∀ᵐ ω ∂μ, IsCadlag (fun t => Y t ω) := by
  have hq := isRealQuasimartingale hX
  refine ⟨rightContModif X, adapted_rightContModif hq, fun t =>
    _root_.Prove2MeSourceProof.h_ce2182052ee14161adc2c6b8 hq t (hrc t), ?_⟩
  filter_upwards [cadlagModif_ae_eq_rightContModif hq] with ω hω
  have h : (fun t => rightContModif X t ω) = fun t => cadlagModif X t ω :=
    funext fun t => (hω t).symm
  rw [h]
  exact isCadlag_cadlagModif ω
end NNReal

section Real

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℝ mΩ} {X : ℝ → Ω → ℝ}

/-- The filtration on nonnegative times obtained by restricting a filtration on `ℝ`. -/
noncomputable def restrictNNReal (ℱ : Filtration ℝ mΩ) : Filtration ℝ≥0 mΩ :=
  ℱ.indexComap NNReal.coe_mono
@[simp] lemma restrictNNReal_apply (ℱ : Filtration ℝ mΩ) (s : ℝ≥0) :
    restrictNNReal ℱ s = ℱ s := rfl
instance [ℱ.IsRightContinuous] : (restrictNNReal ℱ).IsRightContinuous where
  RC s := by
    rw [Filtration.rightCont_eq]
    calc (⨅ r > s, restrictNNReal ℱ r) ≤ ⨅ r > (s : ℝ), ℱ r := by
          refine le_iInf₂ fun r hr => ?_
          have hr0 : (0 : ℝ) ≤ r := s.coe_nonneg.trans hr.le
          exact iInf₂_le_of_le ⟨r, hr0⟩ (NNReal.coe_lt_coe.1 hr) le_rfl
      _ = ℱ.rightCont s := (Filtration.rightCont_eq ℱ s).symm
      _ ≤ ℱ s := Filtration.IsRightContinuous.RC (𝓕 := ℱ) (s : ℝ)
/-- Real-to-nonnegative-real coercion maps the right neighbourhood filter into the right
neighbourhood filter. -/
lemma tendsto_toNNReal_nhdsGT {t : ℝ} (ht : 0 ≤ t) :
    Tendsto Real.toNNReal (𝓝[>] t) (𝓝[>] Real.toNNReal t) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact (continuous_real_toNNReal.tendsto t).mono_left nhdsWithin_le_nhds
  · exact eventually_nhdsWithin_of_forall fun s hs =>
      (Real.toNNReal_lt_toNNReal_iff (ht.trans_lt hs)).2 hs
/-- Real-to-nonnegative-real coercion maps the left neighbourhood filter of a positive time
into the left neighbourhood filter. -/
lemma tendsto_toNNReal_nhdsLT {t : ℝ} (ht : 0 < t) :
    Tendsto Real.toNNReal (𝓝[<] t) (𝓝[<] Real.toNNReal t) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact (continuous_real_toNNReal.tendsto t).mono_left nhdsWithin_le_nhds
  · exact eventually_nhdsWithin_of_forall fun s hs => (Real.toNNReal_lt_toNNReal_iff ht).2 hs
end Real

end LevyStochCalc.Martingale



-- Prove2me | Definitions.Def_SourceProof_41ef9eff4cc7c102f0e2f53b
-- name    : SourceProof_41ef9eff4cc7c102f0e2f53b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:55:44.339789+00:00
-- url     : https://prove2.me/theorems/1b8099c7-47b8-4e49-ba0f-0a59599b7c36
-- title:
--   StochLean source theorem: ProbabilityTheory.isSemimartingale_contDiff_comp_finiteCoordinates

import Definitions.Def_StochLean_ForMathlib_Analysis_FiniteCoordinateDerivatives_F000
import Definitions.Def_SourceProof_00a8a291a5ec377d57feab0f
import Definitions.Def_SourceProof_0f1f1b63b3e52165c8596e25
import Definitions.Def_SourceProof_13d74fe230d87debed607218
import Definitions.Def_SourceProof_264b430747bbe6ee020dbafc
import Definitions.Def_SourceProof_2805187910815ebae4f90f84
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_44c235d61a2cdcb446e715a4
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_7d09eb6a4e03c1fa37d5b869
import Definitions.Def_SourceProof_889cc5878c88eebb9dbc02bf
import Definitions.Def_SourceProof_8c18053bf585bd3a019ad5a3
import Definitions.Def_SourceProof_9a15eada3555a513322a1de0
import Definitions.Def_SourceProof_9e1a38876e8989b923316eb2
import Definitions.Def_SourceProof_aa100ce908969cff7fac9e9d
import Definitions.Def_SourceProof_b8f98f86c80b293137394efa
import Definitions.Def_SourceProof_d306c04c0a492ca797f7a76d
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba
import Definitions.Def_SourceProof_eb46c036c21b7ee898460a06
import Definitions.Def_SourceProof_f4396e898db7f84ef35db80b
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # C2 functions of finitely many cadlag semimartingales are semimartingales

The adapted cadlag residual is identified with the actual finite-variation
jump series. Nonlinear closure is a conclusion, not an input assumption.
-/

@[expose] public section

open MeasureTheory Set Finset StochLean
open scoped NNReal

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_41ef9eff4cc7c102f0e2f53b
    {Ω ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
    {X : ι → ℝ≥0 → Ω → ℝ} {f : (ι → ℝ) → ℝ}
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    IsSemimartingale (fun t ω ↦ f (fun i ↦ X i t ω)) F P := by
  classical
  let ha₁ : ∀ i, Adapted F (fun t ω ↦ StochLean.coordinateDeriv f i (fun j ↦ X j t ω)) :=
    fun i t ↦ (_root_.Prove2MeSourceProof.h_aa100ce908969cff7fac9e9d hf i).continuous.measurable.comp
      (@measurable_pi_lambda _ _ _ (F t) _ _ (fun j ↦ (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 (hX j)) t))
  let hr₁ := fun i ↦ (_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc (_root_.Prove2MeSourceProof.h_889cc5878c88eebb9dbc02bf (fun j ↦ (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 (hX j)))))
    (_root_.Prove2MeSourceProof.h_aa100ce908969cff7fac9e9d hf i).continuous
  let ha₂ : ∀ i j, Adapted F
      (fun t ω ↦ StochLean.coordinateSecondDeriv f i j (fun k ↦ X k t ω)) :=
    fun i j t ↦ (_root_.Prove2MeSourceProof.h_d306c04c0a492ca797f7a76d hf i j).measurable.comp
      (@measurable_pi_lambda _ _ _ (F t) _ _ (fun k ↦ (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 (hX k)) t))
  let hr₂ := fun i j ↦ (_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc (_root_.Prove2MeSourceProof.h_889cc5878c88eebb9dbc02bf (fun k ↦ (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 (hX k)))))
    (_root_.Prove2MeSourceProof.h_d306c04c0a492ca797f7a76d hf i j)
  let J₁ : ℝ≥0 → Ω → ℝ := ∑ i, (hX i).stochasticIntegral hF
    ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (ha₁ i)) hF (hr₁ i)) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (hr₁ i))
  let J₂ : ℝ≥0 → Ω → ℝ := (1 / 2 : ℝ) • ∑ i, ∑ j,
    ((_root_.Prove2MeSourceProof.h_9a15eada3555a513322a1de0 (hX i)) (hX j) hF).stochasticIntegral hF
      ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (ha₂ i j)) hF (hr₂ i j))
      (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (hr₂ i j))
  have hJ₁ : ProbabilityTheory.IsSemimartingale J₁ F P := _root_.Prove2MeSourceProof.h_f4396e898db7f84ef35db80b univ (fun i _ ↦
    (_root_.Prove2MeSourceProof.h_7d09eb6a4e03c1fa37d5b869 (hX i)) hF
      ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (ha₁ i)) hF (hr₁ i)) (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (hr₁ i)))
  have hJ₂ : ProbabilityTheory.IsSemimartingale J₂ F P :=
    (_root_.Prove2MeSourceProof.h_8c18053bf585bd3a019ad5a3 (_root_.Prove2MeSourceProof.h_f4396e898db7f84ef35db80b univ (fun i _ ↦
      _root_.Prove2MeSourceProof.h_f4396e898db7f84ef35db80b univ (fun j _ ↦
        (_root_.Prove2MeSourceProof.h_7d09eb6a4e03c1fa37d5b869 ((_root_.Prove2MeSourceProof.h_9a15eada3555a513322a1de0 (hX i)) (hX j) hF))
          hF
            ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (ha₂ i j)) hF (hr₂ i j))
            (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (hr₂ i j)))))) (1 / 2)
  have ha : Adapted F (fun t ω ↦ f (fun i ↦ X i t ω)) := fun t ↦
    hf.continuous.measurable.comp
      (@measurable_pi_lambda _ _ _ (F t) _ _ (fun i ↦ (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 (hX i)) t))
  have hr := (_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc (_root_.Prove2MeSourceProof.h_889cc5878c88eebb9dbc02bf (fun i ↦ (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 (hX i))))) hf.continuous
  let C₀ : ℝ≥0 → Ω → ℝ := fun _ ω ↦ f (fun i ↦ X i 0 ω)
  have hC : ProbabilityTheory.IsSemimartingale C₀ F P := _root_.Prove2MeSourceProof.h_0f1f1b63b3e52165c8596e25 (ha 0)
  let V : ℝ≥0 → Ω → ℝ := (fun t ω ↦ f (fun i ↦ X i t ω)) - C₀ - J₁ - J₂
  let R : ℝ≥0 → Ω → ℝ := fun t ω ↦ ∑' s : Ioc 0 t,
    StochLean.frechetSecondOrderRemainder f (fun i ↦ ProbabilityTheory.leftLimitProcess (X i) s ω) (fun i ↦ X i s ω)
  have hvR : ProbabilityTheory.HasFiniteVariationPaths R P :=
    _root_.Prove2MeSourceProof.h_b8f98f86c80b293137394efa hX hF hf
  have he : ProbabilityTheory.Indistinguishable V R P := by
    filter_upwards [_root_.Prove2MeSourceProof.h_eb46c036c21b7ee898460a06 hX hF hf] with ω hω t
    have h : f (fun i ↦ X i t ω) - f (fun i ↦ X i 0 ω) =
        J₁ t ω + J₂ t ω + R t ω := by
      simpa only [J₁, J₂, R, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hω t
    change f (fun i ↦ X i t ω) - f (fun i ↦ X i 0 ω) - J₁ t ω - J₂ t ω = R t ω
    linarith only [h]
  have hv : ProbabilityTheory.HasFiniteVariationPaths V P := _root_.Prove2MeSourceProof.h_9e1a38876e8989b923316eb2 (_root_.Prove2MeSourceProof.h_13d74fe230d87debed607218 he) hvR
  have haV : Adapted F V := fun t ↦
    (((ha t).sub ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hC) t)).sub ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hJ₁) t)).sub ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hJ₂) t)
  have hrV : ProbabilityTheory.HasCadlagPaths V P :=
    (_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 ((_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 ((_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 hr) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hC))) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hJ₁))) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hJ₂)
  have hV := (_root_.Prove2MeSourceProof.h_00a8a291a5ec377d57feab0f hv) haV hF hrV
  apply (_root_.Prove2MeSourceProof.h_2805187910815ebae4f90f84 ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hC) ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hJ₁) ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hJ₂) hV)))) _ ha
  exact ae_of_all _ (fun ω t ↦ by
    change f (fun i ↦ X i 0 ω) + (J₁ t ω + (J₂ t ω +
      (f (fun i ↦ X i t ω) - f (fun i ↦ X i 0 ω) - J₁ t ω - J₂ t ω))) = _
    ring)
end ProbabilityTheory



-- Prove2me | Definitions.Def_SourceProof_eb46c036c21b7ee898460a06
-- name    : SourceProof_eb46c036c21b7ee898460a06
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T23:33:52.35438+00:00
-- url     : https://prove2.me/theorems/6b15030d-c051-48e0-89af-82046f5cf8be
-- title:
--   StochLean source theorem: ProbabilityTheory.ito_finiteCoordinates_raw_bracket

import Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F001
import Definitions.Def_SourceProof_15642f07981a3d3f0467a53e
import Definitions.Def_SourceProof_215f6d5e6b10999a8c8f10ba
import Definitions.Def_SourceProof_24278e78a60501166c68bfc8
import Definitions.Def_SourceProof_264b430747bbe6ee020dbafc
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_36da4c661fc115cbdc2bfff4
import Definitions.Def_SourceProof_3c620db59a5da172a27c5abb
import Definitions.Def_SourceProof_5922ecc268414b6fc6aec126
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_60fbb0806e5cb393cb74e054
import Definitions.Def_SourceProof_6335110cda5d685c6e13fff4
import Definitions.Def_SourceProof_6ec6ed103d98506e37900b2a
import Definitions.Def_SourceProof_87f0a7a067d30089e512c6db
import Definitions.Def_SourceProof_889cc5878c88eebb9dbc02bf
import Definitions.Def_SourceProof_9a15eada3555a513322a1de0
import Definitions.Def_SourceProof_aa100ce908969cff7fac9e9d
import Definitions.Def_SourceProof_d306c04c0a492ca797f7a76d
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba
import Definitions.Def_SourceProof_ef39e32da25cd087940fc673
import Definitions.Def_SourceProof_ff07642989734d14cb2ac8eb

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite-dimensional cadlag Ito identity with raw mixed brackets

All ordered Hessian pairs are included. The actual jump remainder is
absolutely summable, and the equality holds on one event for all finite
times. No moments or global derivative bounds are required.
-/

@[expose] public section

open MeasureTheory Filter Set Finset StochLean
open scoped NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*} [Fintype ι] [DecidableEq ι] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 mΩ}
  {X : ι → ℝ≥0 → Ω → ℝ} {f : (ι → ℝ) → ℝ}

theorem _root_.Prove2MeSourceProof.h_eb46c036c21b7ee898460a06
    (hX : ∀ i, IsSemimartingale (X i) F P) (hF : F.IsUsual P) (hf : ContDiff ℝ 2 f) :
    let ha₁ : ∀ i, Adapted F (fun t ω ↦ coordinateDeriv f i (fun j ↦ X j t ω)) :=
      fun i t ↦ (_root_.Prove2MeSourceProof.h_aa100ce908969cff7fac9e9d hf i).continuous.measurable.comp
        (@measurable_pi_lambda _ _ _ (F t) _ _ (fun j ↦ (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 (hX j)) t))
    let hr₁ := fun i ↦ (_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc (_root_.Prove2MeSourceProof.h_889cc5878c88eebb9dbc02bf (fun j ↦ (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 (hX j)))))
      (_root_.Prove2MeSourceProof.h_aa100ce908969cff7fac9e9d hf i).continuous
    let ha₂ : ∀ i j, Adapted F
        (fun t ω ↦ coordinateSecondDeriv f i j (fun k ↦ X k t ω)) :=
      fun i j t ↦ (_root_.Prove2MeSourceProof.h_d306c04c0a492ca797f7a76d hf i j).measurable.comp
        (@measurable_pi_lambda _ _ _ (F t) _ _ (fun k ↦ (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 (hX k)) t))
    let hr₂ := fun i j ↦ (_root_.Prove2MeSourceProof.h_264b430747bbe6ee020dbafc (_root_.Prove2MeSourceProof.h_889cc5878c88eebb9dbc02bf (fun k ↦ (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 (hX k)))))
      (_root_.Prove2MeSourceProof.h_d306c04c0a492ca797f7a76d hf i j)
    Indistinguishable (fun t ω ↦ f (fun i ↦ X i t ω) - f (fun i ↦ X i 0 ω))
      (fun t ω ↦ (∑ i, (hX i).stochasticIntegral hF
          ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (ha₁ i)) hF (hr₁ i))
          (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (hr₁ i)) t ω) +
        (1 / 2 : ℝ) * (∑ i, ∑ j,
          ((_root_.Prove2MeSourceProof.h_9a15eada3555a513322a1de0 (hX i)) (hX j) hF).stochasticIntegral hF
            ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (ha₂ i j)) hF (hr₂ i j))
            (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (hr₂ i j)) t ω) +
        ∑' s : Ioc 0 t,
          frechetSecondOrderRemainder f (fun i ↦ leftLimitProcess (X i) s ω)
            (fun i ↦ X i s ω)) P := by
  dsimp only
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
  let π : ℕ → ProbabilityTheory.StoppingTimePartition F := fun n ↦ ProbabilityTheory.StoppingTimePartition.deterministic F
    ((StochLean.LocallyFinitePartition.dyadic n).restrict (n : ℝ≥0))
  have hπ : ProbabilityTheory.StoppingTimePartition.IsTendingToIdentity π P :=
    _root_.Prove2MeSourceProof.h_6ec6ed103d98506e37900b2a
      _root_.Prove2MeSourceProof.h_36da4c661fc115cbdc2bfff4 tendsto_natCast_atTop_atTop
  have h₁ := _root_.Prove2MeSourceProof.h_ef39e32da25cd087940fc673 univ (fun i _ ↦
    (_root_.Prove2MeSourceProof.h_5922ecc268414b6fc6aec126 (hX i)) hF (ha₁ i) (hr₁ i) hπ)
  have h₂ := _root_.Prove2MeSourceProof.h_ef39e32da25cd087940fc673 univ (fun i _ ↦ _root_.Prove2MeSourceProof.h_ef39e32da25cd087940fc673 univ (fun j _ ↦
    (_root_.Prove2MeSourceProof.h_3c620db59a5da172a27c5abb (hX i)) (hX j) hF (ha₂ i j) (hr₂ i j) hπ))
  have hu := (_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb ((_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb ((_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb ((_root_.Prove2MeSourceProof.h_215f6d5e6b10999a8c8f10ba hπ) (fun t ω ↦ f (fun i ↦ X i t ω))))
    (_root_.Prove2MeSourceProof.h_60fbb0806e5cb393cb74e054 atTop (fun _ ω ↦ f (fun i ↦ X i 0 ω))))) h₁))
      ((_root_.Prove2MeSourceProof.h_24278e78a60501166c68bfc8 h₂) (1 / 2 : ℝ))
  have he := _root_.Prove2MeSourceProof.h_15642f07981a3d3f0467a53e hX hF hf hπ
    ((_root_.Prove2MeSourceProof.h_87f0a7a067d30089e512c6db hu) (fun n ↦ ae_of_all _ (fun ω t ↦ by
      rw [(_root_.Prove2MeSourceProof.h_6335110cda5d685c6e13fff4 (π n))]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply])))
  filter_upwards [he] with ω hω t
  have h := hω t
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h
  linarith only [h]
end ProbabilityTheory



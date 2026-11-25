-- Prove2me | Definitions.Def_SourceProof_6b0aad381fde89d7c19479e6
-- name    : SourceProof_6b0aad381fde89d7c19479e6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:40:03.864279+00:00
-- url     : https://prove2.me/theorems/ec532728-dd13-5958-bfe2-95d7646fffb2
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.adapted_stochasticExponentialJumpProduct

import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticExponential_Basic_F001
import Definitions.Def_SourceProof_0287d90d6966a0a0ba68f0fa
import Definitions.Def_SourceProof_264d677d5da3fcd447059c80
import Definitions.Def_SourceProof_2b2fa01d52a365fcbed78a43
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_46e00cd1de49de31920230f6
import Definitions.Def_SourceProof_472bb0fb2e5ea3f0d733b6e5
import Definitions.Def_SourceProof_4c53178c24a5f39c8484090d
import Definitions.Def_SourceProof_561d7fc50af0bdd1f0a29ad5
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_99d670b7492a1db05d3ba395
import Definitions.Def_SourceProof_c8232beed6b358cd17e7323d
import Definitions.Def_SourceProof_cea06ce35b1a746f3e8af6f7
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Adaptedness of the actual stochastic exponential and jump product

The finite-horizon raw-bracket measure supplies the sample-dependent jump
atoms. Joint measurability uses capped paths and only the horizon sigma-field.
A single initial null set is removed and restored by usual completeness.
Thus adaptedness is proved, not inferred from an uncountable product of
coordinatewise measurable random variables.
-/

@[expose] public section

open MeasureTheory StochLean Set Function
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_6b0aad381fde89d7c19479e6
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Adapted F (stochasticExponentialJumpProduct X) := by
  classical
  obtain ⟨Y, hXY, hYp, hYc⟩ :=
    (_root_.Prove2MeSourceProof.h_c8232beed6b358cd17e7323d (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX).stronglyAdapted) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)
  let D := Classical.choice ((_root_.Prove2MeSourceProof.h_4c53178c24a5f39c8484090d hX) hX hF)
  let G : Ω → Prop := fun ω ↦
    (∀ T : ℝ≥0, Summable (fun s : Ioc 0 T ↦ ProbabilityTheory.jumpProcess Y s ω ^ 2)) ∧
    (∀ s : ℝ≥0, 0 < s → (D.left ω).measure {s} =
      ENNReal.ofReal (ProbabilityTheory.jumpProcess Y s ω ^ 2))
  have hG : ∀ᵐ ω ∂P, G ω := by
    filter_upwards [(_root_.Prove2MeSourceProof.h_472bb0fb2e5ea3f0d733b6e5 hX) hF, (_root_.Prove2MeSourceProof.h_99d670b7492a1db05d3ba395 D),
      (_root_.Prove2MeSourceProof.h_264d677d5da3fcd447059c80 hXY)] with ω hs hm he
    constructor
    · intro T
      simpa only [← he] using hs T
    · intro s hs0
      simpa only [← he] using hm s hs0
  have hbad : MeasurableSet[F 0] {ω | ¬G ω} := (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) _ (ae_iff.mp hG)
  have hgood : MeasurableSet[F 0] {ω | G ω} := by
    simpa only [compl_ofPred, not_not] using hbad.compl
  intro T
  have hcap := (_root_.Prove2MeSourceProof.h_2b2fa01d52a365fcbed78a43 hYp.stronglyAdapted.adapted) hYc T
  have hGT : MeasurableSet[F T] {ω | G ω} := F.mono bot_le _ hgood
  let : MeasurableSpace Ω := F T
  let κ : Kernel Ω ℝ≥0 := ⟨fun ω ↦ (D.left ω).measure.restrict (Iic T),
    _root_.Prove2MeSourceProof.h_cea06ce35b1a746f3e8af6f7 T
      (fun s hs ↦ (D.left_adapted s).mono (F.mono hs) le_rfl)⟩
  have hκ (ω : Ω) : IsFiniteMeasure (κ ω) := by
    refine ⟨?_⟩
    change ((D.left ω).measure.restrict (Iic T)) univ < ⊤
    rw [Measure.restrict_apply_univ, _root_.Prove2MeSourceProof.h_561d7fc50af0bdd1f0a29ad5]
    exact ENNReal.ofReal_lt_top
  let U : Ω → ℝ≥0 → ℝ := fun ω s ↦ if G ω then ProbabilityTheory.jumpProcess Y (min s T) ω else 0
  have hU : Measurable (uncurry U) :=
    Measurable.ite (hGT.preimage measurable_fst) hcap measurable_const
  have hUs (ω : Ω) : Summable (fun s : Ioc 0 T ↦ U ω s ^ 2) := by
    by_cases hg : G ω
    · have he (s : Ioc 0 T) : U ω s = ProbabilityTheory.jumpProcess Y s ω := by
        simp only [U, if_pos hg, min_eq_left s.2.2]
      simpa only [he] using hg.1 T
    · simp only [U, if_neg hg, zero_pow (by decide : 2 ≠ 0)]
      exact summable_zero
  have hUz (ω : Ω) (s : ℝ≥0) (hs : s ∈ Ioc 0 T) (hz : κ ω {s} = 0) :
      U ω s = 0 := by
    by_cases hg : G ω
    · have hm : κ ω {s} = (D.left ω).measure {s} := by
        change ((D.left ω).measure.restrict (Iic T)) {s} = _
        rw [Measure.restrict_apply (measurableSet_singleton s),
          inter_eq_left.mpr (singleton_subset_iff.mpr (Set.mem_Iic.mpr hs.2))]
      have he : ENNReal.ofReal (ProbabilityTheory.jumpProcess Y s ω ^ 2) = 0 :=
        (hg.2 s hs.1).symm.trans (hm.symm.trans hz)
      have hsq : ProbabilityTheory.jumpProcess Y s ω ^ 2 = 0 :=
        le_antisymm (ENNReal.ofReal_eq_zero.mp he) (sq_nonneg _)
      have hj : ProbabilityTheory.jumpProcess Y s ω = 0 := sq_eq_zero_iff.mp hsq
      simp only [U, if_pos hg, min_eq_left hs.2, hj]
    · exact if_neg hg
  have hp := _root_.Prove2MeSourceProof.h_0287d90d6966a0a0ba68f0fa κ hκ T hU hUs hUz
  have he : (fun ω ↦ ∏' s : Ioc 0 T, StochLean.exponentialJumpFactor (U ω s)) =ᵐ[P]
      ProbabilityTheory.stochasticExponentialJumpProduct X T := by
    filter_upwards [hG, (_root_.Prove2MeSourceProof.h_264d677d5da3fcd447059c80 hXY)] with ω hg hj
    apply tprod_congr
    intro s
    simp only [U, if_pos hg, min_eq_left s.2.2, ← hj]
  have hc : MeasureTheory.IsCompleteSubMeasurableSpace P (F T) :=
    fun s hs ↦ F.mono bot_le s ((_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) s hs)
  exact (_root_.Prove2MeSourceProof.h_46e00cd1de49de31920230f6 hc) hp he
end IsSemimartingale

end ProbabilityTheory



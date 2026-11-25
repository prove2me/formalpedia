-- Prove2me | Definitions.Def_SourceProof_578c5291502c2a4d4272ca3a
-- name    : SourceProof_578c5291502c2a4d4272ca3a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:01:28.633675+00:00
-- url     : https://prove2.me/theorems/c91b765c-d9f2-4f3f-8d1b-b8235dcaa8a8
-- title:
--   StochLean source theorem: ProbabilityTheory.CauchyUCP.exists_adapted_cadlag_limit

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Definitions.Def_StochLean_Probability_Process_UCP_Cauchy_F000
import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_884540530c27c62e87bbaba4
import Definitions.Def_SourceProof_9183846313e90de3d6561ee0
import Definitions.Def_SourceProof_a2cb63993a652b5632791121
import Definitions.Def_SourceProof_c1c7541fb1b81dd0ac642a6a
import Definitions.Def_SourceProof_e36e45a75f5c05df94c01778
import Definitions.Def_SourceProof_ec3aa4717c264168127f89f4
import Definitions.Def_SourceProof_f42e2068980787a77fe59ccf
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Sequential UCP completeness for adapted cadlag processes

A summable-probability subsequence is uniformly Cauchy on every compact interval
on one full-measure event. The pointwise limits exist by real completeness and
are locally uniform. An initial-measurable null-set reset makes every path cadlag
and preserves adaptedness. The UCP-Cauchy estimate recovers the whole sequence.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℕ → ℝ≥0 → Ω → ℝ}

namespace CauchyUCP
theorem _root_.Prove2MeSourceProof.h_578c5291502c2a4d4272ca3a [IsFiniteMeasure P]
    (hc : CauchyUCP P X) (ha : ∀ n, Adapted F (X n)) (hF : F.IsUsual P)
    (hr : ∀ n, HasCadlagPaths (X n) P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, Adapted F Y ∧
      (∀ ω, IsCadlagPath (Y · ω)) ∧ TendstoUCP P X atTop Y := by
  classical
  obtain ⟨k, hk, hkc⟩ := (_root_.Prove2MeSourceProof.h_e36e45a75f5c05df94c01778 hc)
  let good : Set Ω := {ω | (∀ n, ProbabilityTheory.IsCadlagPath (X (k n) · ω)) ∧
    ∀ T : ℝ≥0, UniformCauchySeqOn (fun n t ↦ X (k n) t ω) atTop (Icc 0 T)}
  have hg : ∀ᵐ ω ∂P, ω ∈ good := by
    filter_upwards [ae_all_iff.mpr (fun n ↦ hr (k n)), hkc] with ω hω hcω
    exact ⟨hω, hcω⟩
  have hbad : MeasurableSet[F 0] goodᶜ := (_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) goodᶜ (ae_iff.mp hg)
  have hgood : MeasurableSet[F 0] good := by simpa only [compl_compl] using hbad.compl
  let V : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω ↦ if ω ∈ good then X (k n) t ω else 0
  have hVa : ∀ n, Adapted F (V n) := by
    intro n t
    exact Measurable.ite (F.mono bot_le _ hgood) (ha (k n) t) measurable_const
  have hVr : ∀ n ω, ProbabilityTheory.IsCadlagPath (V n · ω) := by
    intro n ω
    by_cases hω : ω ∈ good
    · simpa only [V, if_pos hω] using hω.1 n
    · simpa only [V, if_neg hω] using
        (_root_.Prove2MeSourceProof.h_a2cb63993a652b5632791121 (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))))
  have hVc : ∀ ω T, UniformCauchySeqOn (fun n t ↦ V n t ω) atTop (Icc 0 T) := by
    intro ω T
    by_cases hω : ω ∈ good
    · simpa only [V, if_pos hω] using hω.2 T
    · apply Metric.uniformCauchySeqOn_iff.mpr
      intro ε hε
      exact ⟨0, fun m _ n _ t _ ↦ by simpa only [V, if_neg hω, dist_self] using hε⟩
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ limUnder atTop (fun n ↦ V n t ω)
  have hlim : ∀ t ω, Tendsto (fun n ↦ V n t ω) atTop (𝓝 (Y t ω)) := by
    intro t ω
    exact ((hVc ω t).cauchySeq ⟨bot_le, le_rfl⟩).tendsto_limUnder
  have hVu : ∀ ω T, TendstoUniformlyOn (fun n t ↦ V n t ω) (Y · ω) atTop (Icc 0 T) :=
    fun ω T ↦ (hVc ω T).tendstoUniformlyOn_of_tendsto (fun t _ ↦ hlim t ω)
  have hYa : Adapted F Y := by
    intro t
    let : MeasurableSpace Ω := F t
    exact measurable_of_tendsto_metrizable (fun n ↦ hVa n t)
      (tendsto_pi_nhds.mpr (fun ω ↦ hlim t ω))
  have hYr : ∀ ω, ProbabilityTheory.IsCadlagPath (Y · ω) := fun ω ↦
    _root_.Prove2MeSourceProof.h_c1c7541fb1b81dd0ac642a6a (fun n ↦ hVr n ω) (hVu ω)
  have hVUCP : ProbabilityTheory.TendstoUCP P V atTop Y := by
    apply _root_.Prove2MeSourceProof.h_ec3aa4717c264168127f89f4
      (fun n T ↦ _root_.Prove2MeSourceProof.h_f42e2068980787a77fe59ccf
        (fun t ↦ (hVa n t).mono (F.le t) le_rfl)
        (fun t ↦ (hYa t).mono (F.le t) le_rfl)
        (fun ω ↦ (hVr n ω).1) (fun ω ↦ (hYr ω).1) T)
    exact Eventually.of_forall fun ω T ↦
      _root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0.mpr (hVu ω T)
  have hsub : ProbabilityTheory.TendstoUCP P (X ∘ k) atTop Y := by
    intro T ε hε
    have heq : (fun n ↦ P {ω | ε ≤ ProbabilityTheory.compactDeviation ((X ∘ k) n) Y T ω}) =
        fun n ↦ P {ω | ε ≤ ProbabilityTheory.compactDeviation (V n) Y T ω} := by
      funext n
      apply measure_congr
      filter_upwards [hg] with ω hω
      change (ε ≤ ProbabilityTheory.compactDeviation ((X ∘ k) n) Y T ω) =
        (ε ≤ ProbabilityTheory.compactDeviation (V n) Y T ω)
      simp only [ProbabilityTheory.compactDeviation, Function.comp_apply, V, if_pos hω]
    rw [heq]
    exact hVUCP T ε hε
  exact ⟨Y, hYa, hYr, (_root_.Prove2MeSourceProof.h_884540530c27c62e87bbaba4 hc) hk.tendsto_atTop hsub⟩
end CauchyUCP

end ProbabilityTheory



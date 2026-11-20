-- Prove2me | Definitions.Def_SourceProof_440795d18e40286a66795f61
-- name    : SourceProof_440795d18e40286a66795f61
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:31:47.511173+00:00
-- url     : https://prove2.me/theorems/a51f4738-f70a-406a-be91-51068ed73935
-- title:
--   LevyStochCalc source module: SourceProof_440795d18e40286a66795f61
-- statement:
--   The original source theorem `Measurable.measurableSet_edist_eqOn_zero_of_continuous` comes from the `BrownianMotion.Continuity.KolmogorovChentsov` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Topology_F000
import Definitions.Def_BrownianMotion_Auxiliary_Topology_F001
import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F003
import Definitions.Def_BrownianMotion_Gaussian_StochasticProcesses_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E]

theorem _root_.Prove2MeSourceProof.h_440795d18e40286a66795f61 [SecondCountableTopology T]
    {f g : T → Ω → E} (hU : IsOpen U)
    (hf : ∀ ω, ContinuousOn (f · ω) U) (hg : ∀ ω, ContinuousOn (g · ω) U)
    (h_meas : ∀ t, Measurable (fun ω ↦ edist (f t ω) (g t ω))) :
    MeasurableSet {ω | ∀ t ∈ U, edist (f t ω) (g t ω) = 0} := by
  obtain ⟨T', hT'_countable, hT'_dense⟩ := TopologicalSpace.exists_countable_dense T
  have : {ω | ∀ t ∈ U, edist (f t ω) (g t ω) = 0}
      = {ω | ∀ (t : T'), ↑t ∈ U → edist (f t ω) (g t ω) = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, Subtype.forall]
    refine ⟨fun h t _ ↦ h t, fun h ↦ ?_⟩
    have h_eqOn : Set.EqOn (fun t ↦ edist (f t ω) (g t ω)) 0 (T' ∩ U) := by
      intro t htU
      exact h t htU.1 htU.2
    refine Set.EqOn.of_subset_closure h_eqOn ?_ (by fun_prop) Set.inter_subset_right ?_
    · intro x hx
      exact (hf ω x hx).edist (hg ω x hx)
    · exact subset_closure_dense_inter hT'_dense hU
  rw [this]
  have : {ω | ∀ (t : T'), ↑t ∈ U → edist (f t ω) (g t ω) = 0}
      = ⋂ (t : T') (ht : ↑t ∈ U), {ω | edist (f t ω) (g t ω) = 0} := by ext; simp
  rw [this]
  have : Countable T' := hT'_countable
  refine MeasurableSet.iInter (fun t ↦ ?_)
  by_cases htU : ↑t ∈ U
  · simp only [htU, Set.iInter_true]
    exact StronglyMeasurable.measurableSet_eq_fun (h_meas t).stronglyMeasurable (by fun_prop)
  · simp [htU]
section HolderSet

end HolderSet

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [hE : Nonempty E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

end PseudoEMetricSpace

section EMetricSpace

variable [PseudoEMetricSpace T] [EMetricSpace E] [hE : Nonempty E]

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

end EMetricSpace

end ProbabilityTheory



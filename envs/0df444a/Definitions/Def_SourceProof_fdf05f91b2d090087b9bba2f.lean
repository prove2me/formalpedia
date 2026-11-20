-- Prove2me | Definitions.Def_SourceProof_fdf05f91b2d090087b9bba2f
-- name    : SourceProof_fdf05f91b2d090087b9bba2f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:49:36.008172+00:00
-- url     : https://prove2.me/theorems/3149d2ce-876a-40cd-a9fb-781f1c62447f
-- title:
--   LevyStochCalc source module: SourceProof_fdf05f91b2d090087b9bba2f
-- statement:
--   The original source theorem `ProbabilityTheory.exists_modification_holder_iSup` comes from the `BrownianMotion.Continuity.KolmogorovChentsov` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Topology_F000
import Definitions.Def_BrownianMotion_Auxiliary_Topology_F001
import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F003
import Definitions.Def_BrownianMotion_Gaussian_StochasticProcesses_F000
import Definitions.Def_SourceProof_a8667ac036da36820cd0dc56

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

section HolderSet

end HolderSet

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [hE : Nonempty E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

theorem _root_.Prove2MeSourceProof.h_fdf05f91b2d090087b9bba2f {C : ℕ → Set T} {c : ℕ → ℝ≥0∞} {p q : ℕ → ℝ} {M : ℕ → ℝ≥0}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : ∀ n, IsAEKolmogorovProcess X P (p n) (q n) (M n)) (hc : ∀ n, c n ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : ∀ n, d < q n) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω t (β : ℝ≥0) (_ : 0 < β) (_ : β < ⨆ n, (q n - d) / (p n)),
        ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (Y · ω) U := by
  let X' := (hX 0).mk X
  have hX' : ∀ n, IsKolmogorovProcess X' P (p n) (q n) (M n) := fun n ↦ by
    constructor
    · exact fun s t ↦ (hX 0).IsKolmogorovProcess_mk.measurablePair s t
    · intro s t
      have h_le := (hX n).kolmogorovCondition s t
      refine le_trans (le_of_eq ?_) h_le
      refine lintegral_congr_ae ?_
      filter_upwards [(hX 0).ae_eq_mk s, (hX 0).ae_eq_mk t] with ω hω1 hω2 using by rw [hω1, hω2]
    · exact (hX n).p_pos
    · exact (hX n).q_pos
  obtain ⟨Y, hY_meas, hY_eq, hY_holder⟩ :=
    _root_.Prove2MeSourceProof.h_a8667ac036da36820cd0dc56 hC hX' hc hd_pos hdq_lt
  refine ⟨Y, hY_meas, fun t ↦ ?_, hY_holder⟩
  filter_upwards [ (hX 0).ae_eq_mk t, hY_eq t] with ω hω1 hω2 using hω2.trans hω1.symm
end PseudoEMetricSpace

section EMetricSpace

variable [PseudoEMetricSpace T] [EMetricSpace E] [hE : Nonempty E]

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

end EMetricSpace

end ProbabilityTheory



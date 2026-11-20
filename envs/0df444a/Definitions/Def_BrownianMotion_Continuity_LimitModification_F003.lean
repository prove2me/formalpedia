-- Prove2me | Definitions.Def_BrownianMotion_Continuity_LimitModification_F003
-- name    : BrownianMotion_Continuity_LimitModification_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T07:59:12.636793+00:00
-- url     : https://prove2.me/theorems/d265d217-f030-4c18-aa5d-2c6b78454b4f
-- title:
--   Source declarations: BrownianMotion.Continuity.LimitModification
-- statement:
--   Source-preserving extracted declarations from BrownianMotion.Continuity.LimitModification. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_LimitModification_F001
import Definitions.Def_SourceProof_1bd86707b36fe8af2e0c458d

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
#

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : T → Ω → E} {c : ℝ≥0∞}
  {U : Set T}

section IndicatorProcess

variable {A : Set Ω} [hE : Nonempty E]

end IndicatorProcess

variable [PseudoEMetricSpace E] [hE : Nonempty E]
  [TopologicalSpace T] [SecondCountableTopology T]

lemma IsLimitOfIndicator.measurable_edist
    {T : Type*} [PseudoEMetricSpace T] [SecondCountableTopology T]
    [MeasurableSpace E] [BorelSpace E]
    {Y X Z X' : T → Ω → E} {U₁ U₂ : Set T}
    (hX : ∀ t, Measurable (X t)) (hX' : ∀ t, Measurable (X' t))
    (hX_pair : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X i ω, X' j ω))
    (hY : IsLimitOfIndicator Y X P U₁) (hZ : IsLimitOfIndicator Z X' P U₂)
    (s t : T) :
    Measurable (fun ω ↦ edist (Y s ω) (Z t ω)) := by
  borelize (E × E)
  refine StronglyMeasurable.measurable ?_
  exact continuous_edist.stronglyMeasurable.comp_measurable
    ((fun p2mMethodArg0 p2mMethodArg1 p2mMethodArg2 => _root_.Prove2MeSourceProof.h_1bd86707b36fe8af2e0c458d p2mMethodArg0 p2mMethodArg1 p2mMethodArg2 hY) hX hX' hX_pair hZ s t)
end ProbabilityTheory



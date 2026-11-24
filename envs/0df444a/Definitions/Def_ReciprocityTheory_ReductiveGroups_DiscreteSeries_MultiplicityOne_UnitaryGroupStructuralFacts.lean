-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_UnitaryGroupStructuralFacts
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_UnitaryGroupStructuralFacts
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:49:20.411902+00:00
-- url     : https://prove2.me/theorems/f1846b6d-9341-48f5-a843-21907150c78e
-- title:
--   Unitary Group Structural Facts
-- statement:
--   Definitions and structural lemmas for Unitary Group Structural Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/UnitaryGroupStructuralFacts.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.DS.Mult1
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
def UnitaryGroupStructuralFacts : Prop :=
  ReciprocityTheory.ChartRestriction.DS.Xi.InductiveHeisenbergInputs ∧ RealPlaceDataExists ∧ RankOneCoord ∧ BigCellFactor ∧ UWbFacts ∧ ConjHaar ∧ LemmaBFromXi ∧
    StepJCont ∧ StepPhBound ∧ StepRegBound ∧ StepRegAverage ∧ StepUnfold ∧ AeFromTests ∧ DilJacAll ∧ IntNormB ∧
    Formalism.QuantumDeterminants.UWNormal ∧ Formalism.QuantumDeterminants.EllAdd ∧ Formalism.QuantumDeterminants.NSubgroup
end ReciprocityTheory.ChartRestriction.DS.Mult1



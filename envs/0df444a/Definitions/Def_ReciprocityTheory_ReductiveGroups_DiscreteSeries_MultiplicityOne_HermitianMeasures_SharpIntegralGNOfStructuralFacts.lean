-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_SharpIntegralGNOfStructuralFacts
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_SharpIntegralGNOfStructuralFacts
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:10:28.047728+00:00
-- url     : https://prove2.me/theorems/cb60e369-eee1-423a-9be4-4676713d068e
-- title:
--   Sharp Integral GNOf Structural Facts
-- statement:
--   Definitions and structural lemmas for Sharp Integral GNOf Structural Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/SharpIntegralGNOfStructuralFacts.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_UnitaryGroupStructuralFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A



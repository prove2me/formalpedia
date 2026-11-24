-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergMapContinuous
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergMapContinuous
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:12:48.204161+00:00
-- url     : https://prove2.me/theorems/e10e9141-12d9-47a9-9a50-d9c94d4f5c22
-- title:
--   Heisenberg Map Continuous
-- statement:
--   Definitions and structural lemmas for Heisenberg Map Continuous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergMapContinuous.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ScaleInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergDualBaseVectorFormulaAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
def heisM (k r' : ℕ) : HPar k r' → Mt k (1 + r') := fun x => heis0 k r' x
end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities



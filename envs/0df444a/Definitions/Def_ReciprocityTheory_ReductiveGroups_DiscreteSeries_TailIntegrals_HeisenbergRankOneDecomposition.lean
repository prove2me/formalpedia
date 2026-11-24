-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergRankOneDecomposition
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HeisenbergRankOneDecomposition
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T17:09:31.492105+00:00
-- url     : https://prove2.me/theorems/1fc9a49e-a6b1-490a-bbfd-65d476fae14c
-- title:
--   Heisenberg Rank One Decomposition
-- statement:
--   Definitions and structural lemmas for Heisenberg Rank One Decomposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HeisenbergRankOneDecomposition.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_StarLastDotLast
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
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA



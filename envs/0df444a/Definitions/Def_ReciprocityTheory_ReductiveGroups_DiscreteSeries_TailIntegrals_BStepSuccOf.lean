-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_BStepSuccOf
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_BStepSuccOf
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T17:10:35.79579+00:00
-- url     : https://prove2.me/theorems/cd207e5f-0686-40cd-b6f5-83d4f2f392d6
-- title:
--   BStep Succ Of
-- statement:
--   Definitions and structural lemmas for BStep Succ Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/BStepSuccOf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InnerBound
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
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 BL
end ReciprocityTheory.ChartRestriction.DS.Xi



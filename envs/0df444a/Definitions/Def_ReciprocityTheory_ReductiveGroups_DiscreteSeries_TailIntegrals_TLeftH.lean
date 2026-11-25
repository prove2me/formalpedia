-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TLeftH
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TLeftH
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T14:01:12.058341+00:00
-- url     : https://prove2.me/theorems/95f7660f-ae7a-5010-b946-e3f59270c6b4
-- title:
--   TLeft H
-- statement:
--   Definitions and structural lemmas for TLeft H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/TLeftH.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XphiLinInd
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
open scoped ENNReal NNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B HermitianLiftIdentities
end ReciprocityTheory.ChartRestriction.DS.Xi



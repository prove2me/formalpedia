-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_FockTA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:48.136138+00:00
-- url     : https://prove2.me/theorems/e891b153-62af-4edc-a412-a9505710933a
-- title:
--   Fock TA
-- statement:
--   Definitions and structural lemmas for Fock TA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/FockTA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
section Gen
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
end Gen
section FockLemmas
variable {n : ℕ}
end FockLemmas
end ReciprocityTheory.ChartRestriction.DS



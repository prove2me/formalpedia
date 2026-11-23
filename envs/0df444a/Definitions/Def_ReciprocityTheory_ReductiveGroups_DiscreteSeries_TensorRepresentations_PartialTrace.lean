-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_PartialTrace
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_PartialTrace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:36.417428+00:00
-- url     : https://prove2.me/theorems/601b612f-fcb5-43e5-a401-f7e3d4d579e5
-- title:
--   Partial Trace
-- statement:
--   Definitions and structural lemmas for Partial Trace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/PartialTrace.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_AntiEIsGlRep
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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
def ptr (A : Module.End ℂ (Fin n → M)) : Module.End ℂ M :=
  ∑ c, (coordV c).comp (A.comp (LinearMap.single ℂ (fun _ : Fin n => M) c))
end ReciprocityTheory.ChartRestriction.DS



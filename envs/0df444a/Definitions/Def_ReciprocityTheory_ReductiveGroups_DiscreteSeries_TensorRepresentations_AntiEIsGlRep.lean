-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_AntiEIsGlRep
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_AntiEIsGlRep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:30:12.815821+00:00
-- url     : https://prove2.me/theorems/604b27b5-01e2-4394-b9dc-66b788b156a8
-- title:
--   Anti EIs Gl Rep
-- statement:
--   Definitions and structural lemmas for Anti EIs Gl Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/AntiEIsGlRep.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
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
def antiE (E : Fin n → Fin n → Module.End ℂ M) : Fin n → Fin n → Module.End ℂ M :=
  fun a b => -E (Fin.rev b) (Fin.rev a)
end ReciprocityTheory.ChartRestriction.DS



-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockE
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:08:03.387928+00:00
-- url     : https://prove2.me/theorems/a87accc6-8c17-4189-b203-e4dfeda4e52e
-- title:
--   Low Fock E
-- statement:
--   Definitions and structural lemmas for Low Fock E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/LowFockE.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DSymmHypsInhabited
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeB
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
variable {n : ℕ} {N : Type*} [AddCommGroup N] [Module ℂ N]
def lfLift (ε : Fin n → Bool) (x : LfIdx ε → N) : TensorProduct ℂ N (Fock n) :=
  ∑ S, x S ⊗ₜ[ℂ] fockBasis n S.1
end ReciprocityTheory.ChartRestriction.DS



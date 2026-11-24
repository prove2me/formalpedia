-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:38:28.19005+00:00
-- url     : https://prove2.me/theorems/22605bf6-00ae-4542-9545-4efbc8bc9086
-- title:
--   Highest Weight Differences Nat
-- statement:
--   Definitions and structural lemmas for Highest Weight Differences Nat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/PRVComponents/HighestWeightDifferencesNat.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section SL2
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ M}
end SL2
end ReciprocityTheory.ChartRestriction.DS.HW



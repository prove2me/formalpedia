-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExistsCyclic
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExistsCyclic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:39.383072+00:00
-- url     : https://prove2.me/theorems/d311dc16-680b-47f5-9555-278caf0b583a
-- title:
--   Exists Cyclic
-- statement:
--   Definitions and structural lemmas for Exists Cyclic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExistsCyclic.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
def formV {m : ℕ} (u v : Fin m → ℝ) : ℝ := ∑ s : Fin m, (-1) ^ (s.val + 1) * u s * v s
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N



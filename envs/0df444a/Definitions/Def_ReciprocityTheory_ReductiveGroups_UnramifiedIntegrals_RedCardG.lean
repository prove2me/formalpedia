-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedCardG
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedCardG
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:55:47.607654+00:00
-- url     : https://prove2.me/theorems/2f2063e8-4853-4ee4-a0db-7727b2227091
-- title:
--   Red Card G
-- statement:
--   Definitions and structural lemmas for Red Card G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/RedCardG.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
namespace ReciprocityTheory.ChartRestriction.L1
namespace CardG
def co (L : PeriodPair) (z : ℂ) : ℤ × ℤ :=
  if h : z ∈ L.lattice then
    ((PeriodPair.mem_lattice.mp h).choose, (PeriodPair.mem_lattice.mp h).choose_spec.choose)
  else 0
end CardG
open CardG
end ReciprocityTheory.ChartRestriction.L1



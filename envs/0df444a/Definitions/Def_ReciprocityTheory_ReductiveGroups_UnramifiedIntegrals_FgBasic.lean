-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgBasic
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:32:09.085927+00:00
-- url     : https://prove2.me/theorems/f4dcdb12-fe34-4def-b867-71c7d668c282
-- title:
--   Fg Basic
-- statement:
--   Definitions and structural lemmas for Fg Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgBasic.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K]
section Ring
variable {ι : Type}
end Ring
section OneVar
end OneVar
section Subst
variable {ι : Type}
end Subst
section Frob
variable {l : ℕ} {σ : K →+* K} {ι : Type}
end Frob
end ReciprocityTheory.ChartRestriction.L1



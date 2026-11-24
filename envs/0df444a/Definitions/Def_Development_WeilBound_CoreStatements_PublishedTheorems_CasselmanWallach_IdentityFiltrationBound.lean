-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_IdentityFiltrationBound
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_IdentityFiltrationBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:21.190945+00:00
-- url     : https://prove2.me/theorems/b78d6d74-5b31-4dd3-91ae-fa24f9b4b772
-- title:
--   Identity Filtration Bound
-- statement:
--   Definitions and structural lemmas for Identity Filtration Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/IdentityFiltrationBound.lean

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
namespace PositivityTheory.CW
namespace CommutatorAdjointLower
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
end CommutatorAdjointLower
end PositivityTheory.CW
end



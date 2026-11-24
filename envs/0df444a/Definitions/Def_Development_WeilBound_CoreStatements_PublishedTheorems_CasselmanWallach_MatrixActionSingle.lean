-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_MatrixActionSingle
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_MatrixActionSingle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:51.764018+00:00
-- url     : https://prove2.me/theorems/657ca136-dfc2-41b4-9314-435c7b01d5a4
-- title:
--   Matrix Action Single
-- statement:
--   Definitions and structural lemmas for Matrix Action Single, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/MatrixActionSingle.lean

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
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
namespace SecondMomentAlgebra
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
end SecondMomentAlgebra
end PositivityTheory.CW
end



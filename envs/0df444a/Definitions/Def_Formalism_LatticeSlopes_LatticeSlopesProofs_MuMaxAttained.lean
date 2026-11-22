-- Prove2me | Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxAttained
-- name    : Formalism_LatticeSlopes_LatticeSlopesProofs_MuMaxAttained
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:25.862843+00:00
-- url     : https://prove2.me/theorems/ea9ef92c-ef0d-4af1-afb2-31c500b6fc7c
-- title:
--   Mu Max Attained
-- statement:
--   Definitions and structural lemmas for Mu Max Attained, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/MuMaxAttained.lean

import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
namespace Formalism.F
universe u
section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
end
end Formalism.F



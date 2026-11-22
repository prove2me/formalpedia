-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbitsRefined
-- name    : Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbitsRefined
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:24:37.086262+00:00
-- url     : https://prove2.me/theorems/c35cdcad-c74e-4e5c-8d9d-5deaef3c2e0f
-- title:
--   Many Orbits Refined
-- statement:
--   Definitions and structural lemmas for Many Orbits Refined, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ManyOrbitsRefined.lean

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.G0
namespace CyclicSpanLengthLemmas
open ManyOrbitsP
end CyclicSpanLengthLemmas
end Formalism.G0



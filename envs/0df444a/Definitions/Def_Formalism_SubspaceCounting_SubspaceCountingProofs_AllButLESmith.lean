-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_AllButLESmith
-- name    : Formalism_SubspaceCounting_SubspaceCountingProofs_AllButLESmith
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:18:50.622454+00:00
-- url     : https://prove2.me/theorems/d5f60f50-e721-46a1-955e-a1c615162887
-- title:
--   All But LESmith
-- statement:
--   Definitions and structural lemmas for All But LESmith, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/AllButLESmith.lean

import Definitions.Def_Formalism_SubspaceCounting_StatementD
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
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
open Module
namespace Formalism.G0
namespace AllButLESmithP
variable {O M ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [AddCommGroup M] [Module O M] [Fintype ι]
variable {P : Submodule O M} {n : ℕ}
end AllButLESmithP
end Formalism.G0



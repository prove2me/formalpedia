-- Prove2me | Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex
-- name    : Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:41:51.599926+00:00
-- url     : https://prove2.me/theorems/086b6fd3-a40a-4d9c-8b49-bf4bb0a3c55e
-- title:
--   Subspace Lattice Index
-- statement:
--   Definitions and structural lemmas for Subspace Lattice Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/SubspaceLatticeIndex.lean

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ChainLength
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPowSmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
noncomputable section
namespace Formalism.LatticeIndexTer.subgroupData
variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
end Formalism.LatticeIndexTer.subgroupData
namespace Formalism.LatticeIndexTer
open Formalism.LatticeIndexTer.subgroupData
end Formalism.LatticeIndexTer



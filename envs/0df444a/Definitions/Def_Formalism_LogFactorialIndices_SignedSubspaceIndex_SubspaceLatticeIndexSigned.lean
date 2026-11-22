-- Prove2me | Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
-- name    : Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:48:01.321799+00:00
-- url     : https://prove2.me/theorems/f7b16218-1131-46d6-a856-2c03552c550a
-- title:
--   Subspace Lattice Index Signed
-- statement:
--   Definitions and structural lemmas for Subspace Lattice Index Signed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/SubspaceLatticeIndexSigned.lean

import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open scoped Pointwise
namespace Formalism.LatticeIndexTer.LatticeIndexValuation
end Formalism.LatticeIndexTer.LatticeIndexValuation
namespace Formalism.LatticeIndexTer.LatticeIndexValuation
section Sub
variable {O K X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X]
  [IsScalarTower O K X]
end Sub
end Formalism.LatticeIndexTer.LatticeIndexValuation
namespace Formalism.LatticeIndexTer
open LatticeIndexValuation
end Formalism.LatticeIndexTer



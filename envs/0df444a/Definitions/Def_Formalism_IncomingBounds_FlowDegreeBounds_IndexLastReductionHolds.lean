-- Prove2me | Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_IndexLastReductionHolds
-- name    : Formalism_IncomingBounds_FlowDegreeBounds_IndexLastReductionHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:53:16.451798+00:00
-- url     : https://prove2.me/theorems/f7911a89-8f3c-43d4-93da-c9e917a041bd
-- title:
--   Index Last Reduction Holds
-- statement:
--   Definitions and structural lemmas for Index Last Reduction Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/IndexLastReductionHolds.lean

import Definitions.Def_Formalism_IncomingBounds_IndexLastStep
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndexSigned
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
namespace Formalism.IncomingBounds.LatticeIndexAlt
open Formalism.LatticeIndexTer
variable {O K X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X]
  [IsScalarTower O K X]
end Formalism.IncomingBounds.LatticeIndexAlt
namespace Formalism.IncomingBounds
open Formalism.LatticeIndexTer LatticeIndexAlt
end Formalism.IncomingBounds



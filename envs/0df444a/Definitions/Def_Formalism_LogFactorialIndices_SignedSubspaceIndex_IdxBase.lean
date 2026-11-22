-- Prove2me | Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
-- name    : Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:36:17.861651+00:00
-- url     : https://prove2.me/theorems/1f5c0486-dc20-4002-8651-06ce2e9bde78
-- title:
--   Idx Base
-- statement:
--   Definitions and structural lemmas for Idx Base, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogFactorialIndices/SignedSubspaceIndex/IdxBase.lean

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_GeneralBFactSecondFurther_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LatticeIndexTer
open Module
open scoped Pointwise
namespace LatticeIndexLength
section SlopeTestRemainingChoices
end SlopeTestRemainingChoices
section Sat
variable {O K X : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
end Sat
section Main
end Main
end LatticeIndexLength
open LatticeIndexLength
end Formalism.LatticeIndexTer



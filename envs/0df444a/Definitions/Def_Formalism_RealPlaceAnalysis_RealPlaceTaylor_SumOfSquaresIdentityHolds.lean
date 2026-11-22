-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SumOfSquaresIdentityHolds
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_SumOfSquaresIdentityHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:47:57.316263+00:00
-- url     : https://prove2.me/theorems/e800194a-c502-4210-a6c5-10ec8a6a6fa7
-- title:
--   Sum Of Squares Identity Holds
-- statement:
--   Definitions and structural lemmas for Sum Of Squares Identity Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SumOfSquaresIdentityHolds.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
namespace Formalism.REAL
section WDA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}
end WDA
section WDA2
end WDA2
end Formalism.REAL



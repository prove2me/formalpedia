-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:50:42.192375+00:00
-- url     : https://prove2.me/theorems/20d05f18-3748-4676-8802-a83b32500662
-- title:
--   Is Compact Invariant Compact Span
-- statement:
--   Definitions and structural lemmas for Is Compact Invariant Compact Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IsCompactInvariantCompactSpan.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
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
section KT2Gen
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
end KT2Gen
end Formalism.REAL



-- Prove2me | Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_TwoMulNumDerangementsLeFactorial
-- name    : Formalism_CyclotomicNorms_NonsquarefreeBounds_TwoMulNumDerangementsLeFactorial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:15:42.037494+00:00
-- url     : https://prove2.me/theorems/16602f45-95f4-41c1-86e0-88ebee66884f
-- title:
--   Two Mul Num Derangements Le Factorial
-- statement:
--   Definitions and structural lemmas for Two Mul Num Derangements Le Factorial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/TwoMulNumDerangementsLeFactorial.lean

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace Formalism.CyclotomicNorms.PermutationFixedPoints
def numInv (N a : ℕ) (σ : Equiv.Perm (Fin N)) : ℕ :=
  (((univ : Finset (Fin N)).powersetCard a).filter (fun S => ∀ x, σ x ∈ S ↔ x ∈ S)).card
end Formalism.CyclotomicNorms.PermutationFixedPoints



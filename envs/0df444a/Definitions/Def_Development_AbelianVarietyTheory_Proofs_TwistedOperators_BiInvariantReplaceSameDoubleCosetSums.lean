-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BiInvariantReplaceSameDoubleCosetSums
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_BiInvariantReplaceSameDoubleCosetSums
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:28:46.993042+00:00
-- url     : https://prove2.me/theorems/34da57bb-40c9-4d60-88fa-e0ce9186aef1
-- title:
--   Bi Invariant Replace Same Double Coset Sums
-- statement:
--   Definitions and structural lemmas for Bi Invariant Replace Same Double Coset Sums, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BiInvariantReplaceSameDoubleCosetSums.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
noncomputable section
namespace GlobalTheory.InertZeta
open Formalism.UG
section DosetSwapProof
variable {G : Type} [Group G] {K : Subgroup G}
def dosetOf (K : Subgroup G) (x : G ⧸ K) : Set G :=
  DoubleCoset.doubleCoset x.out (K : Set G) (K : Set G)
end DosetSwapProof
end GlobalTheory.InertZeta
end



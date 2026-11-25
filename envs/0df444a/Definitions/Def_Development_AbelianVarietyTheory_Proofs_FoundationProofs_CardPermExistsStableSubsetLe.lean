-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPermExistsStableSubsetLe
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardPermExistsStableSubsetLe
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:51:50.218806+00:00
-- url     : https://prove2.me/theorems/49ee487b-a641-456e-b2ca-9dd432b0160a
-- title:
--   Card Perm Exists Stable Subset Le
-- statement:
--   Definitions and structural lemmas for Card Perm Exists Stable Subset Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardPermExistsStableSubsetLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FactorialLeTwoMulCardPermWithFixedPointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.StableSubset
open Finset Equiv
noncomputable def wt {N : ℕ} (A : Finset (Fin N)) (σ : Perm (Fin N)) : ℕ :=
  if A.map σ.toEmbedding = A then
    (if (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j then 4 else 8) else 0
end GlobalTheory.StableSubset



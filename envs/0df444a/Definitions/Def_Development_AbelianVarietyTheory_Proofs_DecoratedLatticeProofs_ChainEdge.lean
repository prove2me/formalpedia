-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChainEdge
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChainEdge
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T10:02:06.694843+00:00
-- url     : https://prove2.me/theorems/d6c3ccb8-dfdb-4b7a-bad1-7fe41b5913cc
-- title:
--   Chain Edge
-- statement:
--   Definitions and structural lemmas for Chain Edge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ChainEdge.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory
def chainEdge (k : ℕ) {r : ℕ} (i j : Fin r) : Prop := j.val = i.val + 1 ∧ i.val + 1 ≠ k
instance (k : ℕ) {r : ℕ} : DecidableRel (chainEdge k (r := r)) := fun i j =>
  inferInstanceAs (Decidable (j.val = i.val + 1 ∧ i.val + 1 ≠ k))
example : ¬ chainEdge 1 (0 : Fin 3) 1 ∧ chainEdge 1 (1 : Fin 3) 2 := by decide
end GlobalTheory



-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsPatOne
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsPatOne
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T10:07:19.875256+00:00
-- url     : https://prove2.me/theorems/963889e1-36ae-4db9-b6f4-274fc3f544ef
-- title:
--   Is Pat One
-- statement:
--   Definitions and structural lemmas for Is Pat One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IsPatOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.SymRes
def FreePos (ρ κ i j : ℕ) : Prop :=
  (i < κ ∧ j < κ ∧ i < j) ∨ (κ ≤ i ∧ i < κ + ρ ∧ j < κ) ∨ (i < κ ∧ κ + ρ < j) ∨ (κ ≤ i ∧ i < j)
def IsPat {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) (g : GL (Fin r) K) : Prop :=
  ∀ i j : Fin r, ¬ FreePos ρ κ i.val j.val → g.val i j = (1 : Matrix (Fin r) (Fin r) K) i j
example : FreePos 1 1 1 0 ∧ ¬ FreePos 1 1 0 2 := by unfold FreePos; omega
end GlobalTheory.SymRes



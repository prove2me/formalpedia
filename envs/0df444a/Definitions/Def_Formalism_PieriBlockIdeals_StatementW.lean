-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_StatementW
-- name    : Formalism_PieriBlockIdeals_StatementW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:09.304197+00:00
-- url     : https://prove2.me/theorems/3adb8e19-7494-4a3c-a4a6-249953dfb19a
-- title:
--   Statement W
-- statement:
--   Definitions and structural lemmas for Statement W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/StatementW.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.CohomologicalDescent
open CoxeterSystem
universe u v
def InvSeqAll : Prop :=
  ∀ (B : Type u) (W : Type v) [Group W] (M : CoxeterMatrix B) (cs : CoxeterSystem M W) (w₀ : W),
    (∀ w : W, cs.length w ≤ cs.length w₀) →
    ∀ ω : List B, cs.IsReduced ω → cs.wordProd ω = w₀ →
      (cs.rightInvSeq ω).Nodup ∧ (∀ t : W, t ∈ cs.rightInvSeq ω ↔ cs.IsReflection t) ∧
      (cs.leftInvSeq ω).Nodup ∧ (∀ t : W, t ∈ cs.leftInvSeq ω ↔ cs.IsReflection t) ∧
      ω.length = Nat.card {t : W // cs.IsReflection t}
def adjSwap {n : ℕ} (a : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap a.castSucc a.succ
def wordPerm {n : ℕ} (ω : List (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (ω.map adjSwap).prod
def rightInvSeqA {n : ℕ} : List (Fin n) → List (Equiv.Perm (Fin (n + 1)))
  | [] => []
  | a :: ω => (wordPerm ω)⁻¹ * adjSwap a * wordPerm ω :: rightInvSeqA ω
def InvSeqAllTypeA : Prop :=
  ∀ (n : ℕ) (ω : List (Fin n)), wordPerm ω = Fin.revPerm →
    (∀ ω' : List (Fin n), wordPerm ω' = Fin.revPerm → ω.length ≤ ω'.length) →
      (rightInvSeqA ω).Nodup ∧
      (∀ t : Equiv.Perm (Fin (n + 1)),
        t ∈ rightInvSeqA ω ↔ ∃ i j : Fin (n + 1), i < j ∧ t = Equiv.swap i j) ∧
      ω.length = (n + 1).choose 2
def InvSeqOddTypeA : Prop :=
  ∀ (n : ℕ) (ω : List (Fin n)), wordPerm ω = Fin.revPerm →
    (∀ i j : Fin (n + 1), i < j → Odd ((rightInvSeqA ω).count (Equiv.swap i j))) ∧
      (n + 1).choose 2 ≤ ω.length
end Formalism.CohomologicalDescent



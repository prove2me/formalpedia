-- Prove2me | Definitions.Def_Sensitivity213981Formal_RankExpressions
-- name    : Sensitivity213981Formal_RankExpressions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T18:39:24.094016+00:00
-- url     : https://prove2.me/theorems/90ee1832-65dd-49a1-9656-cdbca098f077
-- title:
--   Rank Expressions — sensitivity certificate definitions
-- statement:
--   The definitions for Rank Expressions in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundRankNumeric.positiveState`, `ThreeBoundRankNumeric.instDecidablePositiveState`, `ThreeBoundRankNumeric.guardState`, `ThreeBoundRankNumeric.instDecidableGuardState`, `ThreeBoundRankNumeric.Possible`, `ThreeBoundRankNumeric.instDecidablePossible`, `ThreeBoundRankNumeric.rankUp`, `ThreeBoundRankNumeric.rankJoint`, `ThreeBoundRankNumeric.stateCost`, `ThreeBoundRankNumeric.rankCost`, `ThreeBoundRankNumeric.possible`, `ThreeBoundRankNumeric.Entry`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; RankExpressions.lean, lines 1–86.

import Definitions.Def_Sensitivity213981Formal_HighTypeCore
import Definitions.Def_Sensitivity213981Formal_MinmaxExpressions
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_RankProfileBounds
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Exact finite rank-state oracle for the q3 min/max upward transfer.
All state tests are actual threshold comparisons; no cost-based pruning. -/


set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

namespace ThreeBoundRankNumeric
open ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundRankProfiles
abbrev Entry := ThreeBoundMinmaxNumeric.Entry

def target (e : Entry) (b x y : ℕ) : Prop :=
  e.lowerAt b ≤  x ∧ e.lowerAt b ≤  y ∧ (e.upperAt b ≤  x ∨ e.upperAt b ≤  y)

instance _root_.Sensitivity213981Formal.ThreeBoundRankNumeric.instDecidableTarget (e : Entry) (b x y : ℕ) : Decidable (target e b x y) :=
  inferInstanceAs (Decidable (e.lowerAt b ≤  x ∧ e.lowerAt b ≤  y ∧
    (e.upperAt b ≤  x ∨ e.upperAt b ≤  y)))

def needed (n : ℕ) (e : Entry) (other b : ℕ) : ℕ :=
  if e.lowerAt b ≤  other then if e.upperAt b ≤  other then e.lowerAt b else e.upperAt b else n

def positiveLevel (k : Fin 11) : Option ℕ :=
  if k.val ≤  3 then some k.val else if 8 ≤  k.val then some (k.val-7) else none

def positiveState (e : Entry) (d x y b : ℕ) : Prop :=
  b ≤  e.tolerance ∧ d=b ∧ ¬ target e b x y ∧ (e.lowerAt b ≤  x ∨ e.lowerAt b ≤  y)

instance _root_.Sensitivity213981Formal.ThreeBoundRankNumeric.instDecidablePositiveState (e : Entry) (d x y b : ℕ) : Decidable (positiveState e d x y b) :=
  inferInstanceAs (Decidable (b ≤  e.tolerance ∧ d=b ∧ ¬ target e b x y ∧
    (e.lowerAt b ≤  x ∨ e.lowerAt b ≤  y)))

def guardState (e : Entry) (d x y b : ℕ) : Prop :=
  b ≤  e.tolerance ∧ d=b+1 ∧ target e b x y

instance _root_.Sensitivity213981Formal.ThreeBoundRankNumeric.instDecidableGuardState (e : Entry) (d x y b : ℕ) : Decidable (guardState e d x y b) :=
  inferInstanceAs (Decidable (b ≤  e.tolerance ∧ d=b+1 ∧ target e b x y))

def Possible (a c : Entry) (k : Fin 11) (x y : ℕ) : Prop :=
  let d := ThreeBoundHighTypes.budget 3 k
  c.guard ≤  x ∧ c.guard ≤  y ∧
  (d ≤  a.tolerance → ¬ target a d x y) ∧
  ThreeBoundHighTypes.OfKind 3 (positiveState c d x y) (guardState c d x y) k

instance _root_.Sensitivity213981Formal.ThreeBoundRankNumeric.instDecidablePossible (a c : Entry) (k : Fin 11) (x y : ℕ) : Decidable (Possible a c k x y) := by
  unfold Possible ThreeBoundHighTypes.OfKind
  infer_instance

def rankUp (n : ℕ) (e : Entry) (p : Option ℕ) (own other : ℕ) : Expr n :=
  match p with
  | none => 0
  | some b =>
    let need := needed n e other b
    if own <  need ∧ need <  n then
      min (pExpr n own need) (jointRankExpr n e.guard own need) else 0

def rankJoint (n : ℕ) (e : Entry) (p : Option ℕ) (own other : ℕ) : Expr n :=
  match p with
  | none => downRankExpr n e.guard own
  | some b =>
    let need := needed n e other b
    if own <  need ∧ need <  n then jointRankExpr n e.guard own need
    else downRankExpr n e.guard own

def stateCost (n : ℕ) (a c : Entry) (k : Fin 11) (x y h : ℕ) : Expr n :=
  let p := positiveLevel k
  let ux := rankUp n c p x y
  let uy := rankUp n c p y x
  let jx := rankJoint n c p x y
  let jy := rankJoint n c p y x
  let c0 := ux+uy
  let c1 := max (if a.guard ≤  x then jx+uy else c0)
    (if a.guard ≤  y then ux+jy else c0)
  if h=0 then c0 else if h=1 then max c0 c1 else
    max (max c0 c1) (if a.guard ≤  x ∧ a.guard ≤  y then jx+jy else c0)

def rankCost (n : ℕ) (a c : Entry) (k : Fin 11) (h : ℕ) : Expr n :=
  Expr.maximum ((List.range n).flatMap fun x => (List.range n).filterMap fun y =>
    if Possible a c k x y then some (stateCost n a c k x y h) else none)

def possible (n : ℕ) (a c : Entry) (k : Fin 11) : Bool :=
  (List.range n).any fun x => (List.range n).any fun y => decide (Possible a c k x y)

end ThreeBoundRankNumeric

end
end Sensitivity213981Formal



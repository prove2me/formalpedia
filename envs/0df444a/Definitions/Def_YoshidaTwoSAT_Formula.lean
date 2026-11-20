-- Prove2me | Definitions.Def_YoshidaTwoSAT_Formula
-- name    : YoshidaTwoSAT_Formula
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-20T01:49:31.472884+00:00
-- url     : https://prove2.me/theorems/4cb82b14-65fd-4db6-bcc4-03bb77389540
-- title:
--   Signed literals, clauses, and distance to satisfiability
-- statement:
--   A formula is a list of clauses on Boolean variables. The distance is the minimum number of clauses violated by any one assignment.
-- source:
--   Yuichi Yoshida, A One-Sided Sublinear-Query Tester for Bounded-Degree 2SAT, https://arxiv.org/abs/2611.16176, pp. 1–2, formula model

import Mathlib.Order.Lattice.Nat

namespace TwoSAT

/-- The sign gives the variable value that makes the literal true. -/
structure Literal (V : Type) where
  var : V
  sign : Bool
  deriving DecidableEq

variable {V : Type}

def Literal.flip (a : Literal V) : Literal V := ⟨a.var, !a.sign⟩
def Literal.eval (a : Literal V) (t : V → Bool) : Bool := t a.var == a.sign

@[simp] theorem Literal.flip_flip (a : Literal V) : a.flip.flip = a := by
  cases a with
  | mk x s => cases s <;> rfl

@[simp] theorem Literal.eval_flip (a : Literal V) (t : V → Bool) :
    a.flip.eval t = !(a.eval t) := by
  rcases a with ⟨x, s⟩
  cases h : t x <;> cases s <;> simp [Literal.eval, Literal.flip, h]

/-- Input normalization represents (a ∨ a) by a unit and (x ∨ ¬x) by taut x. -/
inductive Clause (V : Type) where
  | unit (a : Literal V)
  | taut (x : V)
  | pair (a b : Literal V)
  deriving DecidableEq

def Clause.eval (t : V → Bool) : Clause V → Bool
  | .unit a => a.eval t
  | .taut _ => true
  | .pair a b => a.eval t || b.eval t

def Clause.incident (x : V) : Clause V → Prop
  | .unit a => x = a.var
  | .taut y => x = y
  | .pair a b => x = a.var ∨ x = b.var

def loss (t : V → Bool) : List (Clause V) → ℕ
  | [] => 0
  | c :: cs => (if c.eval t then 0 else 1) + loss t cs

def Satisfiable (F : List (Clause V)) : Prop := ∃ t, loss t F = 0

theorem loss_eq_zero_iff (t : V → Bool) (F : List (Clause V)) :
    loss t F = 0 ↔ ∀ c ∈ F, c.eval t = true := by
  induction F with
  | nil => simp [loss]
  | cons c cs ih => cases h : c.eval t <;> simp [loss, h, ih]

noncomputable def distance (F : List (Clause V)) : ℕ := sInf (Set.range (fun t => loss t F))

end TwoSAT



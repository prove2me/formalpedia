-- Prove2me | Definitions.Def_TruffetCounterexample
-- name    : TruffetCounterexample
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:35.289268+00:00
-- url     : https://prove2.me/theorems/169c1c5e-4e1b-4aed-9937-38ebaf9acd16
-- statement:
--   This block sets up a small max-plus (tropical) elimination framework with two variables and a constant slot, and then records three explicit states. Coefficients lie in the reals with a bottom element ⊥ (WithBot ℝ), a form is a triple of coefficients (columns 0 and 1 for the two variables, column 2 for the constant), and eval(f,w) is the max over k of f(k)+w(k). A row is a pair of forms (lhs, rhs), and a state consists of two rows, a cost form and a predicate saying which variables remain. wellFormed requires that every eliminated variable has coefficient ⊥ in the cost and in both sides of both rows; feasible w means eval(rhs)≤eval(lhs) for each row. For a row i and variable j, lower means the lhs coefficient of j is not ⊥ and the rhs coefficient is strictly smaller, and upper is the mirror condition; dominating j means j remains and has both a lower row and an upper row; eligible(i,j) means j remains, row i is lower for j, and if some variable is dominating then j is dominating. bounded says each remaining variable has a lower or an upper row. stop means rhs(2)≤lhs(2) in every row. switch means all remaining variables have cost ⊥, stop fails, some variable remains, no remaining variable has a lower row, and some remaining variable has an upper row. failure means stop fails and either no variable remains or no remaining variable has a lower row or an upper row. The elimination step uses lowerForm (the rhs of row i shifted by minus the lhs coefficient of j, read as 0 if ⊥, with column j set to ⊥), substitute f j g (column j becomes ⊥, other columns k become max(f k, f(j)+g k)), and cleanup (a row whose rhs is coordinatewise at most its lhs is replaced by the null row with all ⊥). advance(s,i,j) substitutes lowerForm into both sides of every row and into the cost, cleans up the rows, and removes j from the remaining variables. ForcedSingletonStep(s,s',i,j) holds when s and s' are well formed, s is bounded, not stop, not switch and not failure, (i,j) is the unique eligible pair, the substituted cost has some non-⊥ coordinate, and s'=advance(s,i,j). The explicit states are: initial, with row 0 being max(x₀,x₁) versus the constant 0, row 1 being x₀ versus max(1+x₁, −2+constant), cost x₀, and both variables remaining; middle, with row 0 null, row 1 being x₀ versus the constant 1, cost x₀, and only variable 0 remaining; and finalState, with null rows, cost equal to the constant 1, and no variable remaining. crossRowRestriction(s) says that for any two distinct rows i≠r and every real α there is a w with eval(lhs of i)(w) < α + eval(rhs of r)(w). Finally, output=(1,0,0) and better=(0,−1,0) are named vectors. The block contains only definitions, with no stated theorem about them.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TruffetCounterexample.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TruffetCounterexample.lean; bytes 16..3907
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
namespace TruffetV4Counterexample

abbrev Coeff := WithBot ℝ

abbrev Form := Fin 3 → Coeff

abbrev Var := Fin 2

abbrev RowIndex := Fin 2

def column (j : Var) : Fin 3 := ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩

def nullForm : Form := fun _ => ⊥

structure Row where
  lhs : Form
  rhs : Form

structure State where
  rows : RowIndex → Row
  cost : Form
  remaining : Var → Prop

def wellFormed (s : State) : Prop := ∀ j, ¬ s.remaining j →
  s.cost (column j) = ⊥ ∧ ∀ i,
    (s.rows i).lhs (column j) = ⊥ ∧ (s.rows i).rhs (column j) = ⊥

def eval (f : Form) (w : Fin 3 → ℝ) : Coeff :=
  max (f 0 + (w 0 : Coeff)) (max (f 1 + (w 1 : Coeff)) (f 2 + (w 2 : Coeff)))

def feasible (s : State) (w : Fin 3 → ℝ) : Prop :=
  ∀ i, eval (s.rows i).rhs w ≤ eval (s.rows i).lhs w

def lower (s : State) (i : RowIndex) (j : Var) : Prop :=
  (s.rows i).lhs (column j) ≠ ⊥ ∧
    (s.rows i).rhs (column j) < (s.rows i).lhs (column j)

def upper (s : State) (i : RowIndex) (j : Var) : Prop :=
  (s.rows i).rhs (column j) ≠ ⊥ ∧
    (s.rows i).lhs (column j) < (s.rows i).rhs (column j)

def dominating (s : State) (j : Var) : Prop :=
  s.remaining j ∧ (∃ i, lower s i j) ∧ ∃ i, upper s i j

def eligible (s : State) (i : RowIndex) (j : Var) : Prop :=
  s.remaining j ∧ lower s i j ∧ ((∃ k, dominating s k) → dominating s j)

def bounded (s : State) : Prop :=
  ∀ j, s.remaining j → (∃ i, lower s i j) ∨ ∃ i, upper s i j

def stop (s : State) : Prop := ∀ i, (s.rows i).rhs 2 ≤ (s.rows i).lhs 2

def switch (s : State) : Prop :=
  (∀ j, s.remaining j → s.cost (column j) = ⊥) ∧ ¬ stop s ∧
  (∃ j, s.remaining j) ∧
  (¬ ∃ i j, s.remaining j ∧ lower s i j) ∧
  ∃ i j, s.remaining j ∧ upper s i j

def failure (s : State) : Prop := ¬ stop s ∧
  ((¬ ∃ j, s.remaining j) ∨
   ((¬ ∃ i j, s.remaining j ∧ lower s i j) ∧
    (¬ ∃ i j, s.remaining j ∧ upper s i j)))

def lowerForm (s : State) (i : RowIndex) (j : Var) : Form := fun k =>
  if k = column j then ⊥ else
    (s.rows i).rhs k + ((-WithBot.unbotD 0 ((s.rows i).lhs (column j)) : ℝ) : Coeff)

def substitute (f : Form) (j : Var) (g : Form) : Form := fun k =>
  if k = column j then ⊥ else max (f k) (f (column j) + g k)

def cleanup (r : Row) : Row := by
  classical
  exact if ∀ k, r.rhs k ≤ r.lhs k then ⟨nullForm, nullForm⟩ else r

def advance (s : State) (i : RowIndex) (j : Var) : State where
  rows := fun r => cleanup ⟨substitute (s.rows r).lhs j (lowerForm s i j),
    substitute (s.rows r).rhs j (lowerForm s i j)⟩
  cost := substitute s.cost j (lowerForm s i j)
  remaining := fun k => s.remaining k ∧ k ≠ j

def ForcedSingletonStep (s s' : State) (i : RowIndex) (j : Var) : Prop :=
  wellFormed s ∧ wellFormed s' ∧
  bounded s ∧ ¬ stop s ∧ ¬ switch s ∧ ¬ failure s ∧
  (∀ r k, eligible s r k ↔ r = i ∧ k = j) ∧
  (∃ k, (substitute s.cost j (lowerForm s i j)) k ≠ ⊥) ∧
  s' = advance s i j

def initial : State where
  rows := ![⟨![(0 : Coeff), 0, ⊥], ![⊥, ⊥, (0 : Coeff)]⟩,
    ⟨![(0 : Coeff), ⊥, ⊥], ![⊥, (1 : Coeff), ((-2 : ℝ) : Coeff)]⟩]
  cost := ![(0 : Coeff), ⊥, ⊥]
  remaining := fun _ => True

def middle : State where
  rows := ![⟨nullForm, nullForm⟩,
    ⟨![(0 : Coeff), ⊥, ⊥], ![⊥, ⊥, (1 : Coeff)]⟩]
  cost := ![(0 : Coeff), ⊥, ⊥]
  remaining := fun j => j = 0

def finalState : State where
  rows := fun _ => ⟨nullForm, nullForm⟩
  cost := ![⊥, ⊥, (1 : Coeff)]
  remaining := fun _ => False

def crossRowRestriction (s : State) : Prop :=
  ∀ i r : RowIndex, i ≠ r → ∀ α : ℝ, ∃ w : Fin 3 → ℝ,
    eval (s.rows i).lhs w < (α : Coeff) + eval (s.rows r).rhs w

def output : Fin 3 → ℝ := ![1, 0, 0]

def better : Fin 3 → ℝ := ![0, -1, 0]



end TruffetV4Counterexample
end
end OAI



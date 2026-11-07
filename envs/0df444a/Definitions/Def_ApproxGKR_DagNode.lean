-- Prove2me | Definitions.Def_ApproxGKR_DagNode
-- name    : ApproxGKR_DagNode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:05.173013+00:00
-- url     : https://prove2.me/theorems/6750c258-0718-407f-9771-1fcce1a56944
-- title:
--   Numerical computations as directed acyclic graphs and their depth
-- statement:
--   A numerical computation is modelled as a **directed acyclic graph** whose nodes $0,1,2,\dots$ are either inputs (approximate inputs, constants, approximate roots, supplied oracle evaluations) or binary operations $+,-,\times$ applied to two earlier nodes. The **depth** of a node is $0$ at an input and $1+\max$ of its operands' depths at an operation. This is the model of the error-propagation bound of §C.2.
--
--   **Formalization Note** An operation node whose operands are not earlier nodes is ill-formed and gets depth $0$; the theorems that use the model assume well-formedness.
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.2, pp.34–35

import Mathlib

namespace ApproxGKR

/-- The arithmetic operations of a numerical computation over `ℂ`. -/
inductive ArithOp where
  | add
  | sub
  | mul

/-- The exact operation. -/
def ArithOp.eval : ArithOp → ℂ → ℂ → ℂ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

/-- A node of a numerical computation modelled as a directed acyclic graph: an input (an
approximate input, a constant, an approximate root or a supplied oracle evaluation) or a binary
arithmetic operation on two earlier nodes `l`, `r`.

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.2, pp.34–35: "Model each numerical computation as a directed acyclic graph
of arithmetic operations"; "Approximate roots and supplied evaluations of the polynomial extensions
of the wiring predicates are treated as approximate inputs." -/
inductive DagNode where
  | input
  | op (o : ArithOp) (l r : ℕ)

/-- The depth of node `v`: `0` at inputs, `1 + max` of the operands' depths at operations (an
operation whose operands are not earlier nodes is ill-formed and gets depth `0`). -/
def dagDepth (G : ℕ → DagNode) (v : ℕ) : ℕ :=
  match G v with
  | .input => 0
  | .op _ l r => if h : l < v ∧ r < v then max (dagDepth G l) (dagDepth G r) + 1 else 0
termination_by v
decreasing_by all_goals omega

end ApproxGKR



-- Prove2me | Definitions.Def_TwoAgentSched_Timed
-- name    : TwoAgentSched_Timed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:44:38.269256+00:00
-- url     : https://prove2.me/theorems/6f5a08f3-0565-4d5a-9bc8-fd125dbcaac1
-- title:
--   Tick-counting cost monad for the unit-cost RAM model
-- statement:
--   A **timed computation** returning a value of type $\alpha$ is a pair $(\mathrm{val}, \mathrm{cost})$ of a result and a natural number counting the unit-cost steps performed. Sequencing two computations adds their costs; returning a value costs nothing.
--
--   The unit-cost primitives are:
--
--   1. one step (`tick`), used for each list cell traversed, consed or moved and each array access;
--   2. one comparison $a \le b$ in a linear order (reals, extended reals, deadline cuts);
--   3. one addition or subtraction;
--   4. one evaluation $f(t)$ of a cost function, the paper's assumption that each $f^A_h(\cdot)$ value can be computed in constant time;
--   5. one lookup of a precomputed table entry such as a deadline $D^B_k$.
--
--   Two list helpers are built from them: the sum $\sum_{j\in l} p_j$ of a list (one step per addition) and the removal of the first occurrence of an element (one step per cell inspected).
--
--   This is the model in which the running time $O(n_A^2+n_B\log n_B)$ of Theorem 4.1 is counted: every algorithm of this mission is written inside it, so its cost is the number of steps of the same run whose result the theorems describe.
--
--   **Formalization Note** `Timed α` is a structure with fields `val` and `cost`, with a `Monad` instance; `leC`, `addC`, `subC`, `evalC`, `lookupC` are the charged primitives, `sumC` and `eraseC` the list helpers.
-- source:
--   Agnetis, Mirchandani, Pacciarelli, Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2) (2004), §4, pp. 232–233 (running-time analysis: "If we suppose that each f^A_h(·) value can be computed in constant time")

import Mathlib

namespace TwoAgentSched

/-- **A tick-counting cost monad** for the unit-cost RAM model in which Agnetis–Mirchandani–
Pacciarelli–Pacifici, *Scheduling Problems with Two Competing Agents*, Oper. Res. 52(2) (2004),
§4, pp. 232–233, count running time. A computation returns a value `val` and the number `cost`
of unit-cost steps it performed. -/
structure Timed (α : Type) where
  /-- the result -/
  val : α
  /-- the number of unit-cost steps -/
  cost : ℕ

/-- `pure` costs nothing; `bind` adds the costs of both parts. -/
instance : Monad Timed where
  pure a := ⟨a, 0⟩
  bind x f := ⟨(f x.val).val, x.cost + (f x.val).cost⟩

/-- One unit-cost step (one list cell traversed, consed or moved, one array access). -/
def tick : Timed Unit := ⟨(), 1⟩

/-- `k` unit-cost steps. -/
def ticks (k : ℕ) : Timed Unit := ⟨(), k⟩

/-- One comparison `a ≤ b` in a linear order (reals, extended reals, deadline cuts): one step. -/
def leC {κ : Type} [LinearOrder κ] (a b : κ) : Timed Bool := ⟨decide (a ≤ b), 1⟩

/-- One addition: one step. -/
def addC {R : Type} [Add R] (a b : R) : Timed R := ⟨a + b, 1⟩

/-- One subtraction: one step. -/
def subC {R : Type} [Sub R] (a b : R) : Timed R := ⟨a - b, 1⟩

/-- One evaluation `f t` of a cost function, one step (the paper's assumption, p. 233, "that
each `f^A_h(·)` value can be computed in constant time"). -/
def evalC {R S : Type} (f : R → S) (t : R) : Timed S := ⟨f t, 1⟩

/-- One lookup `D k` of a precomputed table (the deadlines), one step. -/
def lookupC {ι S : Type} (D : ι → S) (k : ι) : Timed S := ⟨D k, 1⟩

/-- The sum `∑_{j ∈ l} p j` of a list, one step per addition (one per cell). -/
def sumC {ι R : Type} [Add R] [Zero R] (p : ι → R) : List ι → Timed R
  | [] => pure 0
  | j :: js => do
      let s ← sumC p js
      addC (p j) s

/-- Remove the first occurrence of `x` from a list, one step per cell inspected. -/
def eraseC {ι : Type} [DecidableEq ι] (x : ι) : List ι → Timed (List ι)
  | [] => pure []
  | y :: ys => do
      tick
      if y = x then pure ys else do
        let r ← eraseC x ys
        pure (y :: r)

end TwoAgentSched



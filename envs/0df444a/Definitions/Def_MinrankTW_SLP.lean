-- Prove2me | Definitions.Def_MinrankTW_SLP
-- name    : MinrankTW_SLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:08.512586+00:00
-- url     : https://prove2.me/theorems/1b7c84f2-7612-4eca-87df-b51e0625cc35
-- title:
--   Straight-line programs over a ring with $p$ invertible
-- statement:
--   The model of "arithmetic operations" (Theorem 4) and "coefficient operations" (Proposition 1). A straight-line program is a list of gates evaluated in order, gate $k$ producing register $k$: an input weight, an integer constant, the sum, difference or product of two earlier registers, or an earlier register multiplied by $p^{-1}$, where $p$ is the characteristic of $\mathbb F_q$. Outputs are designated registers.
--
--   The program is evaluated over any commutative ring $A$ given an element $p^{-1}\in A$; the theorems require $p\cdot p^{-1}=1$ in $A$. Inputs and constants are free; the **cost** is the number of arithmetic gates. A program is well formed if every operand is an earlier register and every output is a register. One program is chosen per instance size (no uniformity).
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 4, p.8 and Proposition 1, p.15

import Mathlib

namespace MinrankTW

/-!
# Straight-line programs over a ring in which `p` is invertible

The model of "arithmetic operations" (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), Theorem 4, p.8) and of "coefficient operations"
(Proposition 1, p.15): computations over any commutative ring in which the characteristic `p`
of `F_q` is invertible.

**Formalization Note** A program is a list of gates evaluated in order; gate `k` produces
register `k`. Gates: `input i` (the input weight `i`), `const z` (an integer constant),
`add a b`, `sub a b`, `mul a b` (ring operations on earlier registers `a, b`) and `invp a`
(multiply register `a` by `p⁻¹`). Inputs and constants are free; the cost is the number of
`add`, `sub`, `mul`, `invp` gates. Evaluation takes the ring element `pinv` used by `invp`
(the theorems require `p · pinv = 1`). `WellFormed` requires every operand to be an earlier
register and every output to be a register. One program is chosen per instance size; there is no
uniformity condition.
-/

/-- A gate of a straight-line program with inputs indexed by `ι`. -/
inductive Gate (ι : Type*) where
  | input (i : ι)
  | const (z : ℤ)
  | add (a b : ℕ)
  | sub (a b : ℕ)
  | mul (a b : ℕ)
  | invp (a : ℕ)

/-- A straight-line program with inputs `ι` and outputs `κ`. -/
structure SLP (ι κ : Type*) where
  gates : List (Gate ι)
  out : κ → ℕ

namespace Gate

variable {ι : Type*}

/-- Every operand of the gate is a register below `k`. -/
def RefsBelow : Gate ι → ℕ → Prop
  | input _, _ => True
  | const _, _ => True
  | add a b, k => a < k ∧ b < k
  | sub a b, k => a < k ∧ b < k
  | mul a b, k => a < k ∧ b < k
  | invp a, k => a < k

/-- The gate is an arithmetic operation (it is counted in the cost). -/
def IsOp : Gate ι → Bool
  | input _ => false
  | const _ => false
  | _ => true

/-- The value of the gate given the earlier registers `vals`. -/
def value {R : Type*} [CommRing R] (pinv : R) (inp : ι → R) (vals : List R) : Gate ι → R
  | input i => inp i
  | const z => (z : R)
  | add a b => vals.getD a 0 + vals.getD b 0
  | sub a b => vals.getD a 0 - vals.getD b 0
  | mul a b => vals.getD a 0 * vals.getD b 0
  | invp a => vals.getD a 0 * pinv

end Gate

namespace SLP

variable {ι κ : Type*}

/-- The registers after evaluating the gates in order. -/
def evalGates {R : Type*} [CommRing R] (pinv : R) (inp : ι → R) :
    List (Gate ι) → List R → List R
  | [], vals => vals
  | g :: gs, vals => evalGates pinv inp gs (vals ++ [g.value pinv inp vals])

/-- The outputs of the program on input `inp`, with `pinv` used as `p⁻¹`. -/
def eval {R : Type*} [CommRing R] (P : SLP ι κ) (pinv : R) (inp : ι → R) (o : κ) : R :=
  (evalGates pinv inp P.gates []).getD (P.out o) 0

/-- Operands refer to earlier registers and outputs to registers. -/
def WellFormed (P : SLP ι κ) : Prop :=
  (∀ (k : ℕ) (h : k < P.gates.length), P.gates[k].RefsBelow k) ∧ ∀ o, P.out o < P.gates.length

/-- The number of arithmetic operations. -/
def cost (P : SLP ι κ) : ℕ :=
  P.gates.countP Gate.IsOp

end SLP

end MinrankTW



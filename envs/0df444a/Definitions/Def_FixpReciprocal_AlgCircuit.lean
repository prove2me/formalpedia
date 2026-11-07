-- Prove2me | Definitions.Def_FixpReciprocal_AlgCircuit
-- name    : FixpReciprocal_AlgCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:46:53.810869+00:00
-- url     : https://prove2.me/theorems/dfb22c5d-7790-4ef7-9d69-c3244b6beeb8
-- title:
--   Algebraic circuits (Definition 3.1)
-- statement:
--   An **algebraic circuit** on $\mathbb R^n$ is a finite directed acyclic circuit whose gates apply rational constants and the operations $+,-,\times,\div,\min,\max$. It computes a map $F$ from its $n$ inputs to its $n$ outputs. A circuit is **defined throughout** a set $D$ if every division has a nonzero denominator at every point of $D$.
--
--   The circuit is the way a FIXP instance presents its map, so this is the representation every reduction of the mission reads or writes.
--
--   **Formalization Note** A circuit is a straight-line program: wires $0,\dots,n-1$ are the inputs, the $k$-th operation defines wire $n+k$, and well-formedness says each operation reads only earlier wires, which is acyclicity. Lean's $x/0=0$ must not make an undefined circuit acceptable, so definedness is a separate condition.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), Definition 3.1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_FixpReciprocal_RealSearch

namespace FixpReciprocal

/-- **The operations of an algebraic circuit (Definition 3.1):** rational constants, `+, −, ×, ÷, min, max`.
The arguments are wire indices.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Definition 3.1, p.10. -/
inductive AlgOp where
  | const (q : ℚ)
  | add (i j : ℕ)
  | sub (i j : ℕ)
  | mul (i j : ℕ)
  | div (i j : ℕ)
  | min (i j : ℕ)
  | max (i j : ℕ)

/-- All wire arguments of an operation are below `N`. -/
def AlgOp.ReadsBelow (N : ℕ) : AlgOp → Prop
  | .const _ => True
  | .add i j | .sub i j | .mul i j | .div i j | .min i j | .max i j => i < N ∧ j < N

/-- The value of an operation on the wire values computed so far. -/
noncomputable def AlgOp.eval (w : List ℝ) : AlgOp → ℝ
  | .const q => (q : ℝ)
  | .add i j => w.getD i 0 + w.getD j 0
  | .sub i j => w.getD i 0 - w.getD j 0
  | .mul i j => w.getD i 0 * w.getD j 0
  | .div i j => w.getD i 0 / w.getD j 0
  | .min i j => Min.min (w.getD i 0) (w.getD j 0)
  | .max i j => Max.max (w.getD i 0) (w.getD j 0)

/-- Evaluate operations in order, appending each value as a new wire. -/
noncomputable def runOps : List ℝ → List AlgOp → List ℝ
  | w, [] => w
  | w, op :: ops => runOps (w ++ [op.eval w]) ops

/-- **An algebraic circuit (Definition 3.1)**, as a straight-line program: `n` input wires `0, …, n−1`, the
`k`-th operation defines wire `n + k`, and `out` lists the `n` output wires.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Definition 3.1, p.10: "An algebraic circuit is a finite directed acyclic circuit whose gates
apply the operations listed below."

**Formalization Note.** A straight-line program is a topologically sorted DAG; `AlgCircuit.WellFormed`
is the acyclicity. -/
structure AlgCircuit where
  /-- the dimension -/
  n : ℕ
  /-- the operations, in topological order -/
  ops : List AlgOp
  /-- the output wires -/
  out : List ℕ

/-- Each operation reads only earlier wires (acyclicity), and there are `n` valid output wires. -/
def AlgCircuit.WellFormed (c : AlgCircuit) : Prop :=
  (∀ (k : ℕ) (h : k < c.ops.length), c.ops[k].ReadsBelow (c.n + k)) ∧
  c.out.length = c.n ∧ ∀ o ∈ c.out, o < c.n + c.ops.length

/-- The values of all wires on input `x`. -/
noncomputable def AlgCircuit.wires (c : AlgCircuit) (x : Fin c.n → ℝ) : List ℝ :=
  runOps (List.ofFn x) c.ops

/-- The map `F` computed by the circuit. -/
noncomputable def AlgCircuit.evalOut (c : AlgCircuit) (x : Fin c.n → ℝ) : Fin c.n → ℝ :=
  fun i => (c.wires x).getD (c.out.getD i.val 0) 0

/-- **"Every operation must be defined throughout `D`".** Every division has a nonzero denominator
at every point of `D`.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Definition 3.1, p.10.

**Formalization Note.** Lean's `x / 0 = 0` must not make an undefined circuit acceptable, so this is a
separate clause of a basic instance. Division is the only operation here that can be undefined. -/
def AlgCircuit.DefinedOn (c : AlgCircuit) (D : Set (Fin c.n → ℝ)) : Prop :=
  ∀ x ∈ D, ∀ i j : ℕ, AlgOp.div i j ∈ c.ops → (c.wires x).getD j 0 ≠ 0

end FixpReciprocal



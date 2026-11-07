-- Prove2me | Definitions.Def_SmolenskyAC_Circuit
-- name    : SmolenskyAC_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:09.193212+00:00
-- url     : https://prove2.me/theorems/2026ff74-fd62-43a9-8660-44d8c7c78e20
-- title:
--   Boolean circuits with unbounded fan-in: evaluation, depth, and counts of flagged gates
-- statement:
--   Fix a type $K$ of gate kinds and an interpretation of each kind as an operation. A **circuit** on inputs $X_1,\dots,X_n$ is a list of gates $G_0,\dots,G_{S-1}$; each gate has a kind and a finite list of source wires, and each wire is an input $X_i$, a Boolean constant, or an earlier gate $G_{j'}$ with $j'<j$. A family of output wires, indexed by a type $\iota$, is designated.
--
--   1. **Evaluation.** On an assignment $x\in D^n$ each gate applies its operation to the values of its sources, in order; the circuit computes the values of its output wires.
--   2. **Depth.** Inputs and constants have depth $0$; a gate has depth $1+$ the largest depth of its sources; the depth of the circuit is the largest depth of a gate ($0$ if there is none), i.e. the number of gates on the longest chain of gates.
--   3. **Flagged count.** For a Boolean flag on kinds, the number of gates whose kind is flagged; for the main theorem the flagged kinds are AND and OR.
--
--   This is the circuit model of the paper's Definition on p.78, a finite directed acyclic graph with shared gates.
--
--   **Formalization Note** Gates are listed in a topological order, so every circuit is acyclic by construction. Constants on wires (depth $0$, not gates), repeated wires, empty fan-in and gates that feed no output are allowed; the page's circuits are the special case without them.
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, Basic Notation and Definitions, Definition (Boolean circuit), size and depth, p.78 (pdf 2)

import Mathlib
import Definitions.Def_SmolenskyAC_Operations

namespace SmolenskyAC

/-- A wire of a circuit on `n` inputs whose first `g` gates are already placed: an input
variable `X_i`, a Boolean constant, or (the output of) one of the earlier gates. -/
inductive Wire (n g : ℕ) where
  | input (i : Fin n)
  | const (b : Bool)
  | gate (j : Fin g)
  deriving DecidableEq

/-- A gate whose sources are wires into the inputs, the constants, and the gates placed before it:
a kind (its basic operation) and a finite list of source wires (unbounded fan-in). -/
structure Gate (K : Type*) (n g : ℕ) where
  /-- The basic operation assigned to the gate. -/
  kind : K
  /-- The fan-in. -/
  arity : ℕ
  /-- The source wires, with repetitions allowed. -/
  src : Fin arity → Wire n g

/-- A Boolean circuit on the inputs `X_1, …, X_n` with gate kinds `K` and outputs indexed by `ι`
(Smolensky, STOC 1987, "Basic Notation and Definitions", Definition, p.78).

**Formalization Note.** The page's "transitively closed set" with an operation on each
nonminimal element is a finite directed acyclic graph. Here the gates are listed in a topological
order: gate `j` reads only inputs, constants and gates `< j`, which makes every circuit acyclic by
construction. Against the page this allows Boolean constants on wires (depth `0`, not a gate),
repeated wires, empty fan-in, and gates that feed no output; the page's circuits are the special
case without them. Gates are shared (a DAG, not a formula). -/
structure Circuit (K : Type*) (n : ℕ) (ι : Type*) where
  /-- The number of gates. -/
  size : ℕ
  /-- Gate `j`, whose sources lie among the inputs, the constants and the gates `< j`. -/
  gate : (j : Fin size) → Gate K n j.val
  /-- The output wires. -/
  out : ι → Wire n size

namespace Wire

/-- The value of a wire, given the input assignment `x` and the values `v` of the earlier gates. -/
def eval {n g : ℕ} (x : Cube n) (v : Fin g → Bool) : Wire n g → Bool
  | input i => x i
  | const b => b
  | gate j => v j

/-- The depth of a wire, given the depths `dv` of the earlier gates: inputs and constants have
depth `0`. -/
def depth {n g : ℕ} (dv : Fin g → ℕ) : Wire n g → ℕ
  | input _ => 0
  | const _ => 0
  | gate j => dv j

end Wire

namespace Circuit

/-- The values of the first `k` gates on the assignment `x`, when every kind `κ` is interpreted
as the operation `op κ`. -/
def prefixVals {K : Type*} {n : ℕ} {ι : Type*} (op : K → Operation) (C : Circuit K n ι)
    (x : Cube n) : (k : ℕ) → k ≤ C.size → Fin k → Bool
  | 0, _ => Fin.elim0
  | k + 1, h =>
    Fin.snoc (α := fun _ => Bool) (prefixVals op C x k (Nat.le_of_succ_le h))
      (op (C.gate ⟨k, h⟩).kind (C.gate ⟨k, h⟩).arity
        (fun t => ((C.gate ⟨k, h⟩).src t).eval x (prefixVals op C x k (Nat.le_of_succ_le h))))

/-- The values of all gates on the assignment `x`. -/
def gateVals {K : Type*} {n : ℕ} {ι : Type*} (op : K → Operation) (C : Circuit K n ι)
    (x : Cube n) : Fin C.size → Bool :=
  prefixVals op C x C.size le_rfl

/-- The Boolean function computed by the circuit: output `i` on the assignment `x`
("In a natural way a circuit computes a boolean function", p.78). -/
def eval {K : Type*} {n : ℕ} {ι : Type*} (op : K → Operation) (C : Circuit K n ι)
    (x : Cube n) (i : ι) : Bool :=
  (C.out i).eval x (gateVals op C x)

/-- The depths of the first `k` gates: a gate has depth `1 +` the largest depth of its sources. -/
def prefixDepths {K : Type*} {n : ℕ} {ι : Type*} (C : Circuit K n ι) :
    (k : ℕ) → k ≤ C.size → Fin k → ℕ
  | 0, _ => Fin.elim0
  | k + 1, h =>
    Fin.snoc (α := fun _ => ℕ) (prefixDepths C k (Nat.le_of_succ_le h))
      (1 + Finset.univ.sup (fun t =>
        ((C.gate ⟨k, h⟩).src t).depth (prefixDepths C k (Nat.le_of_succ_le h))))

/-- The depth of every gate: the number of gates on the longest chain of gates ending at it. -/
def gateDepth {K : Type*} {n : ℕ} {ι : Type*} (C : Circuit K n ι) : Fin C.size → ℕ :=
  prefixDepths C C.size le_rfl

/-- The depth of the circuit (p.78): "the length of the longest chain of the gates linearly
ordered by inclusion", the largest gate depth, and `0` for a circuit without gates. -/
def depth {K : Type*} {n : ℕ} {ι : Type*} (C : Circuit K n ι) : ℕ :=
  Finset.univ.sup (gateDepth C)

/-- The number of gates whose kind is flagged: for the goal, the AND and OR gates. -/
def countFlag {K : Type*} {n : ℕ} {ι : Type*} (flag : K → Bool) (C : Circuit K n ι) : ℕ :=
  (Finset.univ.filter fun j : Fin C.size => flag (C.gate j).kind = true).card

end Circuit

end SmolenskyAC



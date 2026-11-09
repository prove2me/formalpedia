-- Prove2me | Definitions.Def_NCFactorClosure607_Circuits_Circuit
-- name    : NCFactorClosure607_Circuits_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:35.652667+00:00
-- url     : https://prove2.me/theorems/b0b386b3-6faf-44e0-b884-ac13ffc06cf7
-- title:
--   Noncommutative arithmetic circuits, gate count, syntactic degree and reversal
-- statement:
--   A **noncommutative arithmetic circuit** over a field $F$ in the variables $X$ is a straight-line program: a nonempty list of gates $G_0,G_1,\dots,G_{s-1}$, where each gate is
--
--   1. a constant input $a$ for an arbitrary $a\in F$,
--   2. a variable input $x\in X$,
--   3. an addition gate $G_i+G_j$, or
--   4. an ordered multiplication gate $G_i\cdot G_j$,
--
--   and the operands of gate $G_k$ are earlier gates ($i,j<k$). A gate may be used as an operand any number of times, so the underlying computation is a directed acyclic graph with sharing (the circuit model; a formula would be the tree case). Each gate computes a polynomial in $F\langle X\rangle$, the multiplication gate computing the product in the stated order; the circuit computes the polynomial of its last gate. There are no division gates, and every field element costs one constant gate.
--
--   The **size** of a circuit is its number of gates. The **syntactic degree** of a gate is $0$ at a constant, $1$ at a variable, the maximum of the operands' at an addition gate and their sum at a multiplication gate; the syntactic degree of a circuit is that of its output gate. The **constants** of a circuit are the field elements at its constant gates.
--
--   The **reversed circuit** is obtained by interchanging the two inputs of every multiplication gate and keeping every other gate.
--
--   **Formalization Note** A circuit is a `List` of gates whose operands are positions in the list; `WellFormed` requires the list to be nonempty and every gate to read only strictly earlier positions. Gate values and syntactic degrees are computed left to right; an out-of-range operand (excluded by `WellFormed`) would read the default value $0$.
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.5, §2, paragraphs Circuit conventions and Reversal; p.5–6, §2.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib

/-!
# Noncommutative arithmetic circuits

Arvind–Joglekar, *Factor Closure in Noncommutative Algebraic Complexity*,
STOC 2027 submission #607, §2, paragraphs "Circuit conventions" and "Reversal", p.5, and §2.1,
p.5–6.

A circuit is a straight-line program: a nonempty list of gates, each gate being a field-constant
input, a variable input, a binary addition, or an ordered binary multiplication whose operands
are *earlier* gates (referred to by their position in the list). Gates may be used as operands
any number of times (sharing), so this is the circuit (DAG) model, not the formula (tree) model.
The size of a circuit is its number of gates, the polynomial it computes is the value of its
last gate. Every element of `F` may appear as a constant at the cost of one gate (§2.1). There
are no division gates.
-/

namespace NCFactorClosure607.Circuits

/-- A gate of a noncommutative circuit. `add i j` and `mul i j` refer to the gates at positions
`i` and `j` of the gate list; `mul i j` computes (value of `i`) * (value of `j`), in this
order. -/
inductive Gate (F : Type*) (X : Type*) where
  | const (a : F)
  | var (x : X)
  | add (i j : ℕ)
  | mul (i j : ℕ)

/-- A noncommutative circuit over `F` in the variables `X`: its list of gates, in topological
order; the last gate is the output. -/
structure Circuit (F : Type*) (X : Type*) where
  gates : List (Gate F X)

namespace Gate

variable {F : Type*} {X : Type*}

/-- The gate reads only gates strictly before position `k`. -/
def OperandsBelow (k : ℕ) : Gate F X → Prop
  | const _ => True
  | var _ => True
  | add i j => i < k ∧ j < k
  | mul i j => i < k ∧ j < k

/-- Value of a gate, given the list `vals` of values of the earlier gates. -/
noncomputable def value [Field F] (vals : List (FreeAlgebra F X)) :
    Gate F X → FreeAlgebra F X
  | const a => algebraMap F (FreeAlgebra F X) a
  | var x => FreeAlgebra.ι F x
  | add i j => vals.getD i 0 + vals.getD j 0
  | mul i j => vals.getD i 0 * vals.getD j 0

/-- Syntactic degree of a gate, given the syntactic degrees of the earlier gates: zero at a
constant, one at a variable, the maximum at an addition gate, the sum at a multiplication gate
(§2, p.5). -/
def synDegree (degs : List ℕ) : Gate F X → ℕ
  | const _ => 0
  | var _ => 1
  | add i j => max (degs.getD i 0) (degs.getD j 0)
  | mul i j => degs.getD i 0 + degs.getD j 0

/-- The reversed gate: the two inputs of a multiplication gate are interchanged; every other
gate is unchanged (§2, paragraph Reversal, p.5). -/
def reverse : Gate F X → Gate F X
  | const a => const a
  | var x => var x
  | add i j => add i j
  | mul i j => mul j i

end Gate

namespace Circuit

variable {F : Type*} {X : Type*}

/-- Well-formedness: the circuit has at least one gate, and every gate reads only earlier
gates. -/
def WellFormed (C : Circuit F X) : Prop :=
  C.gates ≠ [] ∧ ∀ (k : ℕ) (g : Gate F X), C.gates[k]? = some g → g.OperandsBelow k

/-- Size of a circuit: its number of gates. -/
def size (C : Circuit F X) : ℕ := C.gates.length

/-- The values of all gates, in order (gate `k` is evaluated from the values of gates
at positions below `k`). -/
noncomputable def gateValues [Field F] (C : Circuit F X) : List (FreeAlgebra F X) :=
  C.gates.foldl (fun vals g => vals ++ [g.value vals]) []

/-- The polynomial computed by the circuit: the value of its last (output) gate. -/
noncomputable def eval [Field F] (C : Circuit F X) : FreeAlgebra F X :=
  C.gateValues.getLastD 0

/-- The syntactic degrees of all gates, in order. -/
def gateDegrees (C : Circuit F X) : List ℕ :=
  C.gates.foldl (fun degs g => degs ++ [g.synDegree degs]) []

/-- The syntactic degree of the circuit: that of its output gate. -/
def synDeg (C : Circuit F X) : ℕ := C.gateDegrees.getLastD 0

/-- The field constants occurring at the constant input gates of the circuit. -/
def consts (C : Circuit F X) : Set F := {a | Gate.const a ∈ C.gates}

/-- The reversed circuit: interchange the two inputs of every multiplication gate
(§2, paragraph Reversal, p.5). -/
def reverse (C : Circuit F X) : Circuit F X := ⟨C.gates.map Gate.reverse⟩

end Circuit

end NCFactorClosure607.Circuits



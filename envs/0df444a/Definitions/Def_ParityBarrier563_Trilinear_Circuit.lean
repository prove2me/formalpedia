-- Prove2me | Definitions.Def_ParityBarrier563_Trilinear_Circuit
-- name    : ParityBarrier563_Trilinear_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:25.756683+00:00
-- url     : https://prove2.me/theorems/06138d1b-c453-4edc-8678-c223c9099093
-- title:
--   §2 — AND/OR circuits of unbounded fan-in, their size and depth
-- statement:
--   A **circuit** on the variables $V$ consists of AND and OR gates of unbounded fan-in and fan-out. Its gates are numbered $0,1,\dots,s-1$. Gate $i$ has a type (AND or OR) and a finite list of inputs, each of which is a **literal** ($v$ or $\neg v$ for a variable $v\in V$), a Boolean constant, or a gate $j<i$. The list may have any length, so fan-in is unbounded (fan-in zero is allowed: an empty AND is $1$ and an empty OR is $0$). A gate may be read by any number of gates. Because a gate reads only earlier gates, every circuit is acyclic. The **output** is a designated node: a gate, a literal or a constant.
--
--   On input $x\in\{0,1\}^V$ the gates are evaluated in order, and the circuit computes the value of its output node. The **size** of a circuit is its number $s$ of AND and OR gates; literals, negations at the inputs and constants are free. The **depth** of a literal or a constant is $0$, and the depth of a gate is one more than the largest depth among its inputs. The depth of the circuit is the depth of its output, that is, the largest number of gates on a path from an input to the output. A **depth-$d$ circuit** is a circuit of depth at most $d$. Gates that are not connected to the output count toward the size and not toward the depth.
--
--   This is the circuit model of the goal theorem and of the depth reduction (Lemma 2.2) and covering argument (Lemma 5.1). It allows arbitrary DAGs: no layering, alternation or fan-in bound is assumed.
--
--   **Formalization Note** Wires are typed so that gate $i$ can only read gates `Fin i`; evaluation and depth are computed gate by gate. Allowing any output node and gates of fan-in zero only adds circuits, so lower bounds over this class cover the source's circuits.
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, §2 Preliminaries, 'Circuits', printed pp.9–10 (PDF pp.11–12)

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Cube

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-! §2, printed pp.9–10 / PDF 11–12: circuits of AND and OR gates of unbounded fan-in and fan-out
that read literals and constants. Size is the number of AND/OR gates; depth counts gates. -/

/-- The two gate types. -/
inductive GateKind
  | and
  | or
  deriving DecidableEq

/-- A wire source for a gate: a literal (variable `v` with polarity `pos`; `pos = false` is the
negated literal), a Boolean constant, or one of the first `g` gates (`Fin g`).
Gate `i` may only read gates `j < i`, so every circuit is acyclic by construction. -/
inductive Node (V : Type) (g : ℕ)
  | lit (v : V) (pos : Bool)
  | const (c : Bool)
  | gate (j : Fin g)

/-- A circuit on the variables `V`: `size` gates numbered `0, …, size − 1`; gate `i` has a type
and a finite list of inputs (any length, so any fan-in, including zero) among the literals, the
constants and the gates `j < i`; gates may be read by any number of gates (unbounded fan-out).
The output is any node: a gate, a literal or a constant. -/
structure Circuit (V : Type) where
  size : ℕ
  kind : Fin size → GateKind
  inputs : (i : Fin size) → List (Node V i.val)
  output : Node V size

namespace Node

variable {V : Type}

/-- Value of a node at input `x`, given the values `val` of the first `g` gates. -/
def eval {g : ℕ} (x : V → Bool) (val : Fin g → Bool) : Node V g → Bool
  | lit v pos => if pos then x v else !(x v)
  | const c => c
  | gate j => val j

/-- Depth of a node given the depths `dep` of the first `g` gates: literals and constants
have depth `0`. -/
def depth {g : ℕ} (dep : Fin g → ℕ) : Node V g → ℕ
  | lit _ _ => 0
  | const _ => 0
  | gate j => dep j

end Node

namespace Circuit

variable {V : Type}

/-- Value of a gate of the given type on the list of its input values: an AND of an empty list
is `true`, an OR of an empty list is `false`. -/
def applyGate : GateKind → List Bool → Bool
  | .and, l => l.all id
  | .or, l => l.any id

/-- Values of the gates `0, …, i − 1` at input `x`, computed gate by gate. -/
def gateValsUpTo (C : Circuit V) (x : V → Bool) : (i : ℕ) → i ≤ C.size → Fin i → Bool
  | 0, _ => Fin.elim0
  | i + 1, h =>
      let prev := C.gateValsUpTo x i (Nat.le_of_succ_le h)
      Fin.lastCases
        (applyGate (C.kind ⟨i, h⟩) ((C.inputs ⟨i, h⟩).map (Node.eval x prev))) prev

/-- Depths of the gates `0, …, i − 1`: a gate has depth one more than the largest depth among
its inputs (one if it reads only literals and constants or nothing). -/
def gateDepthsUpTo (C : Circuit V) : (i : ℕ) → i ≤ C.size → Fin i → ℕ
  | 0, _ => Fin.elim0
  | i + 1, h =>
      let prev := C.gateDepthsUpTo i (Nat.le_of_succ_le h)
      Fin.lastCases
        (1 + ((C.inputs ⟨i, h⟩).map (Node.depth prev)).foldr max 0) prev

/-- The Boolean function computed by the circuit: the value of its output node. -/
def eval (C : Circuit V) : BoolFn V := fun x =>
  Node.eval x (C.gateValsUpTo x C.size le_rfl) C.output

/-- The depth of the circuit: the largest number of gates on a path from an input (literal or
constant) to the output; gates not connected to the output do not count. A depth-`d` circuit
is one with `depth ≤ d`. -/
def depth (C : Circuit V) : ℕ :=
  Node.depth (C.gateDepthsUpTo C.size le_rfl) C.output

/-- The circuit computes the Boolean function `F`. -/
def Computes (C : Circuit V) (F : BoolFn V) : Prop := ∀ x, C.eval x = F x

/-- The output node is an OR gate. -/
def OutputIsOr (C : Circuit V) : Prop :=
  ∃ i : Fin C.size, C.output = Node.gate i ∧ C.kind i = GateKind.or

end Circuit

end ParityBarrier563.Trilinear



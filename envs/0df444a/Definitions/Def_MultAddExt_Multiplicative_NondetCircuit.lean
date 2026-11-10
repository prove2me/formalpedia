-- Prove2me | Definitions.Def_MultAddExt_Multiplicative_NondetCircuit
-- name    : MultAddExt_Multiplicative_NondetCircuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:46:52.294454+00:00
-- url     : https://prove2.me/theorems/a326fccb-1017-45be-bce8-b1d16eec9df6
-- title:
--   Boolean circuits with the paper's size, nondeterministic circuits and multi-output nondeterministic circuits (Definitions 4.7, 4.9)
-- statement:
--   A **Boolean circuit** $C:\{0,1\}^n\to\{0,1\}^m$ is a sequence of gates, each a fan-in-two AND, a fan-in-two OR or a NOT gate reading inputs or earlier gates (the published `QCSepTotal.Gates`), with fixed Boolean constant wires, together with an input, constant or gate for each of the $m$ outputs. Following the paper (p. 18), its **size** is the number of gates **plus** the number of inputs **plus** the number of outputs.
--
--   A **nondeterministic circuit** with $n$ ordinary inputs (Definition 4.7) is a Boolean circuit $C(x,\mathit{wit})$ on $n+w$ inputs with one output; it computes $f(x)=1$ iff there is a witness $\mathit{wit}\in\{0,1\}^w$ with $C(x,\mathit{wit})=1$. We write $C(x)=1$ in that case. Its size counts the $w$ witness bits as inputs.
--
--   A **multi-output nondeterministic circuit** (Definition 4.9) with outputs in $\{0,1\}^o$ is a Boolean circuit $C(x,\mathit{wit})$ with $o+1$ outputs: the last says whether it accepts, the others are the element it outputs. Its set of accepted outputs is
--   $$\mathrm{ACCEPT}_C(x)=\{a\in\{0,1\}^o : \exists\,\mathit{wit},\ C(x,\mathit{wit}) \text{ accepts and outputs } a\}.$$
--   $C$ is single-valued and computes $g$ when $\mathrm{ACCEPT}_C(x)=\{g(x)\}$ for every $x$.
--
--   These are the samplers, postselection predicates and reconstruction circuits of the mission, and the circuits against which the hardness assumption is stated.
--
--   **Formalization Note** Gates are typed so that every wire reference is well formed. The two Boolean constants are fixed wires, not ordinary or witness inputs. They allow circuits with no inputs to compute either constant. Only the variable input lengths are counted in the size; choosing constant gates instead changes size by at most two.
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), p. 18 (PDF 22), size convention; §4.2.1, p. 19 (PDF 23), Definitions 4.7 and 4.9

import Mathlib
import Definitions.Def_QCSepTotal_Circuit

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-! # Boolean circuits with the paper's size; nondeterministic circuits (Definitions 4.7, 4.9)

Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, *Multiplicative and Additive Extractors for Low
Entropy Samplable Sources Under Reduced Assumptions*, STOC 2027 submission (manuscript sha256
5ac077d7…), p. 18 (PDF 22) and §4.2.1, p. 19 (PDF 23).

Gates are the published `QCSepTotal.Gates`: fan-in-two AND and OR gates and NOT gates, each reading
inputs or strictly earlier gates. "The size of a circuit, deterministic or nondeterministic,
includes its input, output, and witness lengths" (p. 18). -/

/-- A deterministic Boolean circuit with `n` inputs and `m` outputs: `numGates` gates (fan-in-two
AND/OR, NOT), with fixed Boolean constant wires; each output is an input, a constant, or a gate. -/
structure Circ (n m : ℕ) where
  /-- the number of gates -/
  numGates : ℕ
  /-- the gates, in topological order, with Boolean constants supplied as fixed wires -/
  gates : QCSepTotal.Gates (Fin n ⊕ Bool) numGates
  /-- the wire read by each output -/
  out : Fin m → (Fin n ⊕ Bool) ⊕ Fin numGates

/-- The output of a circuit on `x ∈ {0,1}ⁿ`. -/
def Circ.eval {n m : ℕ} (C : Circ n m) (x : Fin n → Bool) : Fin m → Bool :=
  fun j => Sum.elim (Sum.elim x id) (C.gates.vals (Sum.elim x id)) (C.out j)

/-- The size of a circuit (p. 18): gates plus inputs plus outputs. -/
def Circ.size {n m : ℕ} (C : Circ n m) : ℕ := C.numGates + n + m

/-- A **nondeterministic circuit** with `n` ordinary inputs (Definition 4.7): a Boolean circuit
`C(x, wit)` on `n + w` inputs with one output. -/
structure NondetCirc (n : ℕ) where
  /-- the witness length -/
  w : ℕ
  /-- the underlying deterministic circuit on `(x, wit)` -/
  C : Circ (n + w) 1

/-- `C(x) = 1` for a nondeterministic circuit: some witness makes the circuit output `1`. -/
def NondetCirc.accepts {n : ℕ} (C : NondetCirc n) (x : Fin n → Bool) : Prop :=
  ∃ wit : Fin C.w → Bool, C.C.eval (Fin.append x wit) 0 = true

/-- Size of a nondeterministic circuit: gates + (ordinary inputs + witness bits) + output. -/
def NondetCirc.size {n : ℕ} (C : NondetCirc n) : ℕ := C.C.size

/-- A **multi-output nondeterministic circuit** (Definition 4.9) with `n` ordinary inputs and outputs
in `{0,1}^o`: a deterministic circuit `C(x, wit)` with `o + 1` outputs; the last output says whether
it accepts, the first `o` outputs are the element it outputs. -/
structure MultiNondetCirc (n o : ℕ) where
  /-- the witness length -/
  w : ℕ
  /-- the underlying deterministic circuit -/
  C : Circ (n + w) (o + 1)

/-- `ACCEPT_C(x) = {a : ∃ wit, C(x, wit) accepts and outputs a}` (Definition 4.9). -/
def MultiNondetCirc.acceptSet {n o : ℕ} (C : MultiNondetCirc n o) (x : Fin n → Bool) :
    Set (Fin o → Bool) :=
  {a | ∃ wit : Fin C.w → Bool, C.C.eval (Fin.append x wit) (Fin.last o) = true ∧
    ∀ j : Fin o, C.C.eval (Fin.append x wit) (Fin.castSucc j) = a j}

/-- Size of a multi-output nondeterministic circuit: gates + inputs + witness bits + outputs. -/
def MultiNondetCirc.size {n o : ℕ} (C : MultiNondetCirc n o) : ℕ := C.C.size

end MultAddExt.Multiplicative



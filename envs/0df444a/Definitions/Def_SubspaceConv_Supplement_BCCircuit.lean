-- Prove2me | Definitions.Def_SubspaceConv_Supplement_BCCircuit
-- name    : SubspaceConv_Supplement_BCCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:46:44.166383+00:00
-- url     : https://prove2.me/theorems/63789a3c-aaad-4638-9cf1-35e84944b380
-- title:
--   Bounded-coefficient linear circuits over $\mathbb C$
-- statement:
--   A **bounded-coefficient linear circuit** over $\mathbb C$ is a list of gates, each either reading an input entry (free) or computing
--
--   $$z = \alpha x + \beta y, \qquad \alpha, \beta \in \mathbb C,\ |\alpha|, |\beta| \le 1,$$
--
--   from two earlier registers $x, y$ (possibly the same one), together with an output register for every output index. Its **size** is the number of gates $z = \alpha x + \beta y$.
--
--   This is Morgenstern's model, in which Theorem 7 proves the $\Omega_q(v \log v)$ lower bound for the incidence transform $I_{4r}^{r,3r}$.
--
--   **Formalization Note** Well-formedness requires earlier operands, outputs that are registers, and complex modulus at most $1$ on both coefficients of every gate.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4e583122875209a3e25ee95aa3a7af933526e165d47c274634e604ab2), App. F, Theorem 7, p.26 (PDF p.27)

import Mathlib

set_option autoImplicit false

namespace SubspaceConv.Supplement

/-!
# Bounded-coefficient linear circuits over `ℂ`

The model of Theorem 7 of Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), App. F, p.26 (PDF p.27): gates of the form `z = αx + βy`
with `|α|, |β| ≤ 1`.

**Formalization Note** A circuit is a list of gates evaluated in order; gate `k` produces register
`k`. `input i` reads an input entry (free); `lin α a β b` computes `α · x_a + β · x_b` from two
earlier registers (`a = b` allowed). Outputs are designated registers. `WellFormed` requires earlier
operands, outputs that are registers, and `‖α‖ ≤ 1`, `‖β‖ ≤ 1` (complex modulus) on every `lin`
gate. `size` is the number of `lin` gates.
-/

/-- A gate of a bounded-coefficient linear circuit with inputs `ι`. -/
inductive BCGate (ι : Type*) where
  | input (i : ι)
  | lin (α : ℂ) (a : ℕ) (β : ℂ) (b : ℕ)

/-- A linear circuit over `ℂ` with inputs `ι` and outputs `κ`. -/
structure BCCircuit (ι κ : Type*) where
  gates : List (BCGate ι)
  out : κ → ℕ

namespace BCGate

variable {ι : Type*}

/-- The gate's operands are registers below `k` and its coefficients have modulus at most 1. -/
def Admissible : BCGate ι → ℕ → Prop
  | input _, _ => True
  | lin α a β b, k => a < k ∧ b < k ∧ ‖α‖ ≤ 1 ∧ ‖β‖ ≤ 1

/-- The gate is a `lin` gate (it is counted in the size). -/
def IsLin : BCGate ι → Bool
  | input _ => false
  | lin _ _ _ _ => true

/-- The value of the gate given the earlier registers `vals`. -/
def value (inp : ι → ℂ) (vals : List ℂ) : BCGate ι → ℂ
  | input i => inp i
  | lin α a β b => α * vals.getD a 0 + β * vals.getD b 0

end BCGate

namespace BCCircuit

variable {ι κ : Type*}

/-- The registers after evaluating the gates in order. -/
def evalGates (inp : ι → ℂ) : List (BCGate ι) → List ℂ → List ℂ
  | [], vals => vals
  | g :: gs, vals => evalGates inp gs (vals ++ [g.value inp vals])

/-- The outputs of the circuit on the input table `inp`. -/
def eval (P : BCCircuit ι κ) (inp : ι → ℂ) (o : κ) : ℂ :=
  (evalGates inp P.gates []).getD (P.out o) 0

/-- Earlier operands, coefficients of modulus at most 1, and outputs that are registers. -/
def WellFormed (P : BCCircuit ι κ) : Prop :=
  (∀ (k : ℕ) (h : k < P.gates.length), P.gates[k].Admissible k) ∧ ∀ o, P.out o < P.gates.length

/-- The number of gates `z = αx + βy`. -/
def size (P : BCCircuit ι κ) : ℕ :=
  P.gates.countP BCGate.IsLin

end BCCircuit

end SubspaceConv.Supplement



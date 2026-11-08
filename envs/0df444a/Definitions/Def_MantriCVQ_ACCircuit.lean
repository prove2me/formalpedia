-- Prove2me | Definitions.Def_MantriCVQ_ACCircuit
-- name    : MantriCVQ_ACCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:20.830607+00:00
-- url     : https://prove2.me/theorems/bd5d8662-1907-42d4-a901-d3e2cf49493e
-- title:
--   Constant-depth circuits: AND, OR, input negations
-- statement:
--   A **circuit** consists of AND and OR gates of unbounded fan-in with negations at the inputs, and constants may appear as inputs. Each gate reads literals, constants and earlier gates. The **depth** is the number of gates on a longest path from an input to the output, and the **size** is the number of gates plus the number of wires into gates.
--
--   **Formalization Note** Gates may be shared, so this is a general circuit (a directed acyclic graph), not only a formula.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3, p. 13 (PDF p. 15)

import Mathlib

namespace MantriCVQ

/-- An input of a gate of a circuit: a literal (`(v, true)` is `x_v`, `(v, false)` is `¬x_v`), a
constant, or an earlier gate. -/
inductive Src (V : Type) where
  | lit (v : V) (b : Bool)
  | const (b : Bool)
  | gate (i : ℕ)

/-- A gate: AND (`isAnd = true`) or OR of a list of inputs. -/
structure ACGate (V : Type) where
  /-- whether the gate is an AND -/
  isAnd : Bool
  /-- the inputs of the gate -/
  inputs : List (Src V)

/-- A circuit (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §3, p. 13 (PDF p. 15): "A circuit
consists of AND and OR gates of unbounded fan-in with negations at the inputs, and constants may also
appear as inputs"): a list of gates, each reading literals, constants and earlier gates, and an
output.

**Formalization Note** Gates may be shared, so this is a general circuit (a directed acyclic graph),
not only a formula. -/
structure ACCircuit (V : Type) where
  /-- the gates, in topological order -/
  gates : List (ACGate V)
  /-- the output -/
  output : Src V
  wf : ∀ (k : ℕ) (hk : k < gates.length), ∀ s ∈ gates[k].inputs, ∀ i : ℕ, s = .gate i → i < k
  wf_output : ∀ i : ℕ, output = .gate i → i < gates.length

/-- The value of an input, given the values of the earlier gates. -/
def Src.eval {V : Type} (x : V → Bool) (vals : List Bool) : Src V → Bool
  | .lit v b => x v == b
  | .const b => b
  | .gate i => vals.getD i false

/-- The value of a circuit at the assignment `x`. -/
def ACCircuit.eval {V : Type} (F : ACCircuit V) (x : V → Bool) : Bool :=
  F.output.eval x <| F.gates.foldl (fun vals g =>
    vals ++ [if g.isAnd then g.inputs.all (Src.eval x vals) else g.inputs.any (Src.eval x vals)]) []

/-- The number of gates on a longest path ending at an input, given the depths of the earlier gates;
a literal or constant has depth `0`. -/
def Src.depth {V : Type} (ds : List ℕ) : Src V → ℕ
  | .lit _ _ => 0
  | .const _ => 0
  | .gate i => ds.getD i 0

/-- The depth of a circuit (§3, p. 13: "the number of gates on a longest path from an input to the
output"). -/
def ACCircuit.depth {V : Type} (F : ACCircuit V) : ℕ :=
  F.output.depth <| F.gates.foldl (fun ds g =>
    ds ++ [1 + (g.inputs.map (Src.depth ds)).foldr max 0]) []

/-- The size of a circuit (§3, p. 13: "its size is the number of gates and wires"): the number of
gates plus the total fan-in. -/
def ACCircuit.size {V : Type} (F : ACCircuit V) : ℕ :=
  F.gates.length + (F.gates.map fun g => g.inputs.length).sum

end MantriCVQ



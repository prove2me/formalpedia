-- Prove2me | Definitions.Def_CEPolytopeHard_GCircuit
-- name    : CEPolytopeHard_GCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:25.250366+00:00
-- url     : https://prove2.me/theorems/21e38f95-ecce-4947-9256-2f0b8df77a09
-- title:
--   Generalized circuit and gate satisfaction at tolerance $\tau$
-- statement:
--   A **generalized circuit** on $d$ nodes lists one gate per node: node $i$ is the output of gate $i$. Gates have at most two inputs and cycles are allowed. The gate types are constant $\beta$, scaling by $\beta$, copying, addition, subtraction and comparison. The circuit is **well formed** when all inputs are nodes and every parameter $\beta$ is a rational in $[0, 1]$, and it has **fan-out two** when every node occurs in at most two input positions (counted with multiplicity).
--
--   For an assignment $v \in \mathbb R^d$ with input values $a, b$ and output value $c = v_i$, gate $i$ is **satisfied at tolerance $\tau$** when
--
--   1. constant: $|c - \beta| \le \tau$;
--   2. scaling: $|c - \beta a| \le \tau$;
--   3. copying: $|c - a| \le \tau$;
--   4. addition: $|c - \min\{a + b, 1\}| \le \tau$;
--   5. subtraction: $|c - \max\{a - b, 0\}| \le \tau$;
--   6. comparison: $a < b - \tau \Rightarrow c \ge 1 - \tau$ and $a > b + \tau \Rightarrow c \le \tau$.
--
--   These circuits are the input of Assumption 2.2 and of the hardness result [71] used in Theorem 4(i).
--
--   **Formalization Note** Inputs are 0-based node indices; a missing or out-of-range input has value $0$ (excluded by well-formedness).
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Section 2.5, p.12

import Mathlib

set_option autoImplicit false

namespace CEPolytopeHard

/-- A gate of a **generalized circuit** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang,
*The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version
of November 2, 2026, sha256 6aec500a…7820, Section 2.5, p.12): constant `β`, scaling by `β`,
copying, addition, subtraction and comparison. Input nodes are given by their 0-based index. -/
inductive GGate where
  | const (β : ℚ)
  | scale (β : ℚ) (a : ℕ)
  | copy (a : ℕ)
  | add (a b : ℕ)
  | sub (a b : ℕ)
  | cmp (a b : ℕ)

namespace GGate

/-- the first input of a gate, if any -/
def argA : GGate → Option ℕ
  | const _ => none
  | scale _ a => some a
  | copy a => some a
  | add a _ => some a
  | sub a _ => some a
  | cmp a _ => some a

/-- the second input of a gate, if any -/
def argB : GGate → Option ℕ
  | add _ b => some b
  | sub _ b => some b
  | cmp _ b => some b
  | _ => none

/-- the input positions of a gate, in order (a node used twice occurs twice) -/
def inputs (g : GGate) : List ℕ := g.argA.toList ++ g.argB.toList

/-- the parameter `β` of a gate, if any -/
def param : GGate → Option ℚ
  | const β => some β
  | scale β _ => some β
  | _ => none

end GGate

/-- A **generalized circuit** (Section 2.5, p.12: "A generalized circuit assigns a value in
[0, 1] to each of d nodes, each of which is the output of exactly one gate. Gates have at most two
inputs and cycles are allowed"): node `i` is the output of gate `i`, so the circuit is the list of
its `d` gates. -/
structure GCircuit where
  /-- gate `i` computes node `i` -/
  gates : List GGate

namespace GCircuit

/-- the number of nodes `d` -/
abbrev d (C : GCircuit) : ℕ := C.gates.length

/-- **Well-formedness**: every input index is a node, and every gate parameter is a rational
number in `[0, 1]` ("All gate parameters β are rational numbers in [0, 1]", p.12). -/
def WellFormed (C : GCircuit) : Prop :=
  ∀ g ∈ C.gates, (∀ a ∈ g.inputs, a < C.d) ∧ ∀ β ∈ g.param, 0 ≤ β ∧ β ≤ 1

/-- **Fan-out two** (p.12: "The circuit has fan-out two if each node occurs in at most two input
positions"): input positions are counted with multiplicity. -/
def FanOutTwo (C : GCircuit) : Prop :=
  ∀ v : ℕ, (C.gates.flatMap GGate.inputs).count v ≤ 2

/-- the value of node `a` under an assignment `v` (`0` for an index that is not a node, excluded by
`WellFormed`) -/
def val (C : GCircuit) (v : Fin C.d → ℝ) (a : ℕ) : ℝ := if h : a < C.d then v ⟨a, h⟩ else 0

/-- the value of an optional input (`0` when the gate has no such input) -/
def valO (C : GCircuit) (v : Fin C.d → ℝ) : Option ℕ → ℝ
  | none => 0
  | some a => C.val v a

end GCircuit

/-- **Gate satisfaction at tolerance τ** (Section 2.5, p.12): with input values `a, b` and output
value `c = v_i`, the gate computing node `i` is satisfied when
constant: `|c − β| ≤ τ`; scaling: `|c − βa| ≤ τ`; copying: `|c − a| ≤ τ`;
addition: `|c − min{a + b, 1}| ≤ τ`; subtraction: `|c − max{a − b, 0}| ≤ τ`; and comparison:
`a < b − τ ⟹ c ≥ 1 − τ` and `a > b + τ ⟹ c ≤ τ`. -/
def GateSat (τ : ℝ) (C : GCircuit) (v : Fin C.d → ℝ) (i : Fin C.d) : Prop :=
  match C.gates.get i with
  | .const β => |v i - (β : ℝ)| ≤ τ
  | .scale β a => |v i - (β : ℝ) * C.val v a| ≤ τ
  | .copy a => |v i - C.val v a| ≤ τ
  | .add a b => |v i - min (C.val v a + C.val v b) 1| ≤ τ
  | .sub a b => |v i - max (C.val v a - C.val v b) 0| ≤ τ
  | .cmp a b => (C.val v a < C.val v b - τ → 1 - τ ≤ v i) ∧ (C.val v b + τ < C.val v a → v i ≤ τ)

end CEPolytopeHard



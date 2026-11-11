-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_Circuit
-- name    : PPADSIS_SubexpSIS_Circuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:46:09.008743+00:00
-- url     : https://prove2.me/theorems/aa7d3179-07eb-4ca5-9d3b-dc7e9cb07a23
-- title:
--   Boolean circuits: gates, well-formedness, evaluation, size counting input wires, description
-- statement:
--   A **Boolean circuit** has $n_{\mathrm{in}}$ input wires numbered $0,\dots,n_{\mathrm{in}}-1$, a list of gates in topological order (gate $k$ writes wire $n_{\mathrm{in}}+k$), and an ordered list of output wires. A gate is a constant $0$ or $1$, a negation $\neg w_i$, a conjunction $w_i\wedge w_j$, or a disjunction $w_i\vee w_j$. The circuit is **well formed** if gate $k$ reads only inputs and earlier gates (so the circuit is acyclic), every output names an existing wire, and the output wires are distinct (as in the standard model, an output is a node of the circuit, so a circuit has at most $|C|$ outputs; a value wanted twice is copied by a gate). On an input $x\in\{0,1\}^{n_{\mathrm{in}}}$ the wire values are computed gate by gate, and the output is the list of the values of the output wires, so the circuit computes a map $\{0,1\}^{n_{\mathrm{in}}}\to\{0,1\}^{\#\text{outputs}}$.
--
--   The **size** counts the input wires as well as the gates,
--   $$|C| = n_{\mathrm{in}} + \#\text{gates},$$
--   as Definition 3.8 prescribes ("the size of a Boolean circuit counts its input wires as well as its gates").
--
--   The **description** of a circuit, given to algorithms and adversaries, is `encNat` of the numbers of inputs and gates, the gate codes (a two-bit tag, then the constant or the wires read), `encNat` of the number of outputs and the output wires. It is injective and of length $O(|C|\log|C|)$.
--
--   **Formalization Note** The published `ConstrSOSP.Circuit` was not reused: its well-formedness forces exactly as many outputs as inputs (the meter circuit $M$ needs $m+1$ outputs, the verifier $V$ one) and it has no constant gates. Wires read out of range evaluate to $0$; on well-formed circuits with inputs of the right length no index is out of range.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), pp. 20-22, Definitions 3.1, 3.2 (Boolean circuits) and Definition 3.8 (size convention)

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Encoding

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

/-- A gate of a Boolean circuit: a constant, a negation, a binary conjunction or a binary
disjunction. Wires are numbered: the inputs are wires `0, …, nIn − 1`, and the `k`-th gate writes
wire `nIn + k`; a gate names the wires it reads. -/
inductive Gate where
  | const (b : Bool)
  | not (i : ℕ)
  | and (i j : ℕ)
  | or (i j : ℕ)

/-- A **Boolean circuit** (Choudhuri, *PPAD Hardness from SIS*, STOC 2027 submission (manuscript
sha256 17abad73…), §3, pp. 20–22): `nIn` input wires, the gates in topological order (gate `k`
writes wire `nIn + k`), and the ordered list `outs` of output wires. A circuit computes a map
`{0,1}^nIn → {0,1}^(outs.length)`. -/
structure Circuit where
  nIn : ℕ
  gates : List Gate
  outs : List ℕ

/-- Gate well-formedness when `k` wires (the inputs and the earlier gates) are available: every
wire it reads is one of them. -/
def Gate.WF (k : ℕ) : Gate → Prop
  | .const _ => True
  | .not i => i < k
  | .and i j => i < k ∧ j < k
  | .or i j => i < k ∧ j < k

/-- A circuit is **well formed**: the `k`-th gate reads only inputs and earlier gates (so the
circuit is acyclic), every output names an existing wire, and the output wires are distinct (an
output is a node of the circuit, as in the standard model, so the number of outputs is at most the
size; a value wanted twice is copied by a gate). -/
def Circuit.WF (C : Circuit) : Prop :=
  (∀ k (hk : k < C.gates.length), (C.gates[k]'hk).WF (C.nIn + k)) ∧
    (∀ o ∈ C.outs, o < C.nIn + C.gates.length) ∧ C.outs.Nodup

/-- The value of a gate, given the values `ws` of the wires before it. -/
def Gate.value (ws : List Bool) : Gate → Bool
  | .const b => b
  | .not i => !(ws.getD i false)
  | .and i j => ws.getD i false && ws.getD j false
  | .or i j => ws.getD i false || ws.getD j false

/-- **Evaluation** of a circuit on an input string `x` (of length `nIn` for a well-formed use):
the wire values are computed gate by gate, and the output is the list of the values of the output
wires. -/
def Circuit.eval (C : Circuit) (x : List Bool) : List Bool :=
  let ws := C.gates.foldl (fun ws g => ws ++ [g.value ws]) x
  C.outs.map (fun o => ws.getD o false)

/-- The **size** of a Boolean circuit counts its input wires as well as its gates (Definition 3.8,
p. 22: "the size of a Boolean circuit counts its input wires as well as its gates"). -/
def Circuit.size (C : Circuit) : ℕ := C.nIn + C.gates.length

/-- Binary code of a gate: a two-bit tag, then the constant or the wires read (`encNat`). -/
def Gate.enc : Gate → List Bool
  | .const b => [false, false, b]
  | .not i => [false, true] ++ encNat i
  | .and i j => [true, false] ++ encNat i ++ encNat j
  | .or i j => [true, true] ++ encNat i ++ encNat j

/-- The **description** of a circuit, as given to algorithms and adversaries: `encNat` of the
number of inputs and of gates, the gate codes, `encNat` of the number of outputs, and the output
wires. It is prefix-free and injective, and its length is `O(|C| log |C|)`. -/
def Circuit.enc (C : Circuit) : List Bool :=
  encNat C.nIn ++ encNat C.gates.length ++ C.gates.flatMap Gate.enc ++
    encNat C.outs.length ++ C.outs.flatMap encNat

end PPADSIS.SubexpSIS



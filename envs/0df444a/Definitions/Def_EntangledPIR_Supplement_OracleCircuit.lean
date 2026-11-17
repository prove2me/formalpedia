-- Prove2me | Definitions.Def_EntangledPIR_Supplement_OracleCircuit
-- name    : EntangledPIR_Supplement_OracleCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:28:04.62984+00:00
-- url     : https://prove2.me/theorems/acb245df-b738-46b3-bf8c-b48f2c0b6b3e
-- title:
--   Boolean oracle circuits, nondeterministic oracle circuits, their size and the relation $V^O$
-- statement:
--   Fix a Boolean oracle $O:\{0,1\}^*\to\{0,1\}$. A **deterministic Boolean oracle circuit** has a number of input wires and a list of gates, evaluated in order. Each gate is one of the following:
--
--   1. a constant, which is a fixed advice bit;
--   2. a wire from an input;
--   3. a non-oracle gate $\mathrm{NOT}$, $\mathrm{AND}$ or $\mathrm{OR}$ of fan-in at most two, reading earlier gates;
--   4. an oracle gate, which reads its query string $q$ from explicit wires of earlier gates and outputs $O(q)$.
--
--   Some gates are designated as outputs.
--
--   The **size** of a circuit counts its input wires (input, witness and transcript bits), its gates (fixed constants included), the wires entering the gates (query wires included) and its output wires.
--
--   A **nondeterministic oracle circuit** $V$ with inputs $x\in\{0,1\}^n$ and $y\in\{0,1\}^b$ is such a circuit whose input is $x$, then $y$, then a witness $w$. It **computes the relation**
--   $$V^O(x,y)\iff \exists w:\ V(x,y,w)=1 .$$
--   Its size counts the witness bits as inputs.
--
--   These circuits state the hypothesis (8.4) of Theorem 8.2 and measure the $R$-boundedness of a protocol.
--
--   **Formalization Note** A gate refers to earlier gates by their position. A reference to a gate that is not earlier reads $0$, so every circuit is acyclic and its evaluation is total. The basis (fan-in-two $\mathrm{AND}$/$\mathrm{OR}$ and $\mathrm{NOT}$, with constants) is one bounded-fan-in basis; another basis changes sizes only by a constant factor, which the existential constant $c_{\mathrm{rel}}$ of Theorem 8.2 absorbs. The circuit "outputs one" when its output list is exactly $[1]$.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026), sha256 5cfce27c325365d29c042cf08ea41ddd83b9a5c0f711ef85e2620d8955251384, §8.1, p.41 (PDF p.43) (nondeterministic oracle circuits and their size); App. D.2, p.61 (PDF p.63) (size of the simulating circuit)

import Definitions.Def_EntangledPIR_Bits

namespace EntangledPIR

namespace Supplement

/-- A gate of a Boolean oracle circuit, Mantri, *Private Information Retrieval from Two Entangled
Servers*, manuscript (Nov. 2026), §8.1, p.41 (PDF p.43): a constant (a fixed advice bit), a wire from
input `i`, a non-oracle gate of fan-in at most two (`NOT`, `AND`, `OR`), or an oracle gate that reads
its query string from the explicit wires `q`. Gates refer to earlier gates by their position. -/
inductive OGate : Type where
  | const (v : Bool)
  | input (i : ℕ)
  | not (a : ℕ)
  | and (a c : ℕ)
  | or (a c : ℕ)
  | oracle (q : List ℕ)

/-- The number of wires entering a gate (for an oracle gate, its query wires). -/
def OGate.fanIn : OGate → ℕ
  | .const _ => 0
  | .input _ => 1
  | .not _ => 1
  | .and _ _ => 2
  | .or _ _ => 2
  | .oracle q => q.length

/-- The value of a gate, given the oracle `O : {0,1}* → {0,1}`, the input bits `inp` and the values
`acc` of the earlier gates. A reference to a gate that is not earlier reads `false`, so every circuit is
acyclic. -/
def OGate.eval (O : List Bool → Bool) (inp acc : List Bool) : OGate → Bool
  | .const v => v
  | .input i => inp.getD i false
  | .not a => !(acc.getD a false)
  | .and a c => acc.getD a false && acc.getD c false
  | .or a c => acc.getD a false || acc.getD c false
  | .oracle q => O (q.map fun w => acc.getD w false)

/-- **A deterministic Boolean oracle circuit**, §8.1, p.41 (PDF p.43): `numIn` input wires, a list of
gates evaluated in order, and a list of output gates. -/
structure OracleCircuit where
  /-- the number of input bits -/
  numIn : ℕ
  /-- the gates, in topological order -/
  gates : List OGate
  /-- the output wires (positions of gates) -/
  outs : List ℕ

/-- The values of all gates on input `inp`. -/
def OracleCircuit.values (O : List Bool → Bool) (C : OracleCircuit) (inp : List Bool) : List Bool :=
  C.gates.foldl (fun acc g => acc ++ [g.eval O inp acc]) []

/-- The output bits of `C` on input `inp`. -/
def OracleCircuit.eval (O : List Bool → Bool) (C : OracleCircuit) (inp : List Bool) : List Bool :=
  C.outs.map fun w => (C.values O inp).getD w false

/-- **The size** of a circuit, §8.1, p.41 and App. D.2, p.61: it counts the input wires (input,
witness and transcript bits), the gates (constant gates are the fixed advice and other constants), the
wires entering the gates (query wires included), and the output wires. -/
def OracleCircuit.size (C : OracleCircuit) : ℕ :=
  C.numIn + C.gates.length + (C.gates.map OGate.fanIn).sum + C.outs.length

/-- **A nondeterministic oracle circuit** with inputs `x ∈ {0,1}^n`, `y ∈ {0,1}^b`, §8.1, p.41: a
deterministic oracle circuit whose input is `x`, then `y`, then a witness of `wit` bits. -/
structure NondetCircuit (n b : ℕ) where
  /-- the underlying deterministic circuit -/
  circ : OracleCircuit
  /-- the number of witness bits -/
  wit : ℕ
  /-- its inputs are `x`, `y` and the witness -/
  numIn_eq : circ.numIn = n + b + wit

/-- The size of a nondeterministic circuit: that of the underlying circuit, which counts the witness
bits among its inputs. -/
def NondetCircuit.size {n b : ℕ} (V : NondetCircuit n b) : ℕ := V.circ.size

/-- **The relation `V^O` computed by `V`**, §8.1, p.41: it holds at `(x, y)` when some witness makes
the circuit output one (its output list is the single bit `1`). -/
def NondetCircuit.Rel (O : List Bool → Bool) {n b : ℕ} (V : NondetCircuit n b) (x : Bits n)
    (y : Bits b) : Prop :=
  ∃ w : Bits V.wit, V.circ.eval O (List.ofFn x ++ List.ofFn y ++ List.ofFn w) = [true]

end Supplement

end EntangledPIR



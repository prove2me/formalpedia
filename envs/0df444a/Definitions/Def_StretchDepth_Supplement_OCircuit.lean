-- Prove2me | Definitions.Def_StretchDepth_Supplement_OCircuit
-- name    : StretchDepth_Supplement_OCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:11:19.298484+00:00
-- url     : https://prove2.me/theorems/941dc604-a414-4271-87c4-aed421d3371a
-- title:
--   Oracle circuits, their size (wires) and depth (§2.2)
-- statement:
--   An **oracle circuit** $C:\{0,1\}^n\to\{0,1\}$ is a circuit whose gates are $\neg$, $\vee$, $\wedge$ of fan-in $1,2,2$, or **oracle gates** of arbitrary fan-in. For an oracle $O:\{0,1\}^*\to\{0,1\}$, $C^O$ is obtained by substituting $O$ into the oracle gates: an oracle gate whose inputs carry $b_1,\dots,b_a$ outputs $O(b_1\cdots b_a)$.
--
--   1. The **size** $|C|$ is the number of wires of $C$.
--   2. The **depth** $\mathrm{depth}(C)$ is the length of the longest path of wires from the output to some input.
--
--   The circuit is given as a list of gates in topological order, each reading the inputs and earlier gates, with a designated output node; it also carries a prefix-free string description $\langle C\rangle$ (used for $\mathrm{SAT}^O$).
--
--   **Formalization Note** Size is the total fan-in of all gates. A node from which no path reaches an input (such as an oracle gate of fan-in $0$) has depth $0$, so the measure is never larger than under the usual conventions. The description writes $n$, the output node, the number of gates and every gate argument in unary, which is polynomially related to a binary code.
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), §2.2, p.15 (PDF p.15)

import Mathlib

set_option autoImplicit false

namespace StretchDepth.Supplement

/-- A gate of an oracle circuit. Arguments are node indices: nodes `0, …, n-1` are the inputs and
node `n + j` is gate `j`. `not`, `or`, `and` have fan-in 1, 2, 2; an oracle gate has arbitrary
fan-in (its argument list, in order, is the oracle query). -/
inductive OGate where
  /-- `¬` of one node -/
  | not (a : ℕ)
  /-- `∨` of two nodes -/
  | or (a b : ℕ)
  /-- `∧` of two nodes -/
  | and (a b : ℕ)
  /-- an oracle gate of arbitrary fan-in -/
  | oracle (args : List ℕ)

/-- The nodes a gate reads, one per incoming wire. -/
def OGate.args : OGate → List ℕ
  | .not a => [a]
  | .or a b => [a, b]
  | .and a b => [a, b]
  | .oracle as => as

/-- **Oracle circuit on `n` inputs** (§2.2, p.15): a list of gates, each reading only inputs and
earlier gates, and an output node. -/
structure OCircuit (n : ℕ) where
  /-- the gates, in topological order -/
  gates : List OGate
  /-- the output node -/
  out : ℕ
  /-- gate `j` reads only nodes `< n + j` (inputs and earlier gates) -/
  args_lt : ∀ (j : ℕ) (h : j < gates.length), ∀ a ∈ (gates.get ⟨j, h⟩).args, a < n + j
  /-- the output is a node -/
  out_lt : out < n + gates.length

/-- The value of a gate, given the values `v` of the earlier nodes and the oracle `O`. -/
def OGate.evalWith (O : List Bool → Bool) (v : List Bool) : OGate → Bool
  | .not a => !(v.getD a false)
  | .or a b => v.getD a false || v.getD b false
  | .and a b => v.getD a false && v.getD b false
  | .oracle as => O (as.map fun a => v.getD a false)

variable {n : ℕ}

/-- The values of all nodes on input `x` (`x` of length `n`), inputs first. -/
def OCircuit.values (O : List Bool → Bool) (C : OCircuit n) (x : List Bool) : List Bool :=
  C.gates.foldl (fun v g => v ++ [g.evalWith O v]) x

/-- `C^O(x)`: the value of the output node, the oracle `O` substituted into the oracle gates. -/
def OCircuit.eval (O : List Bool → Bool) (C : OCircuit n) (x : List Bool) : Bool :=
  (C.values O x).getD C.out false

/-- `|C|`: the number of wires, i.e. the total fan-in of all gates. -/
def OCircuit.size (C : OCircuit n) : ℕ :=
  (C.gates.map fun g => g.args.length).sum

/-- For every node, whether some path of wires leads from it to an input, and the length of the
longest such path (`0` for an input, and for a node with no path to an input). -/
def OCircuit.pathInfo (C : OCircuit n) : List (Bool × ℕ) :=
  C.gates.foldl
    (fun info g =>
      let ch := g.args.map fun a => info.getD a (false, 0)
      info ++ [(ch.any (·.1), (ch.map fun p => if p.1 then p.2 + 1 else 0).foldr max 0)])
    (List.replicate n (true, 0))

/-- **Oracle circuit, size and depth.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), §2.2, p.15: "An "oracle circuit" C^(·) : {0,1}^n → {0,1} is a circuit in which
each gate is either one of {¬, ∨, ∧} of fan-in 1,2,2 respectively, or else an "oracle gate" which
can have arbitrary fan-in. The total size of C, denoted |C|, is the number of wires in the circuit
C. The depth of C, denoted depth(C), is the length of the longest path of wires from the output to
some input."

`depth(C)` is the length of the longest path of wires from the output node to an input node.

**Formalization Note.** Size counts wires (the total fan-in of all gates), not gates. The depth is
the length of the longest path that ends at an input; a node with no such path (e.g. an oracle
gate of fan-in `0`) has depth `0`, so a circuit's depth is never larger than under the usual
conventions (the paper's footnote 9 says its measure is "slightly more restrictive"). There are no
constant gates (none are listed on the page; a fan-in-`0` oracle gate is the oracle's value on the
empty string). -/
def OCircuit.depth (C : OCircuit n) : ℕ :=
  (C.pathInfo.getD C.out (false, 0)).2

/-- Unary code of a natural number: `k` ones and a zero. -/
def unaryCode (k : ℕ) : List Bool := List.replicate k true ++ [false]

/-- The code of a gate: a two-bit tag, then its arguments in unary (an oracle gate first gives its
fan-in). -/
def OGate.encode : OGate → List Bool
  | .not a => [false, false] ++ unaryCode a
  | .or a b => [false, true] ++ unaryCode a ++ unaryCode b
  | .and a b => [true, false] ++ unaryCode a ++ unaryCode b
  | .oracle as => [true, true] ++ unaryCode as.length ++ as.flatMap unaryCode

/-- The string description of an oracle circuit: `n`, the output node and the number of gates in
unary, then the gates. A prefix-free code, parsable in polynomial time; its length is polynomial in
the size of the circuit and `n`. -/
def OCircuit.encode (C : OCircuit n) : List Bool :=
  unaryCode n ++ unaryCode C.out ++ unaryCode C.gates.length ++ C.gates.flatMap OGate.encode

end StretchDepth.Supplement



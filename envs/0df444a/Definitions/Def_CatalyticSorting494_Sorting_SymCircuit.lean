-- Prove2me | Definitions.Def_CatalyticSorting494_Sorting_SymCircuit
-- name    : CatalyticSorting494_Sorting_SymCircuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:19.316967+00:00
-- url     : https://prove2.me/theorems/e75a8fab-0409-44f9-a001-c5eae343f306
-- title:
--   Circuits of symmetric gates of arbitrary fan-in, their evaluation, size and input encoding
-- statement:
--   A function $f:\{0,1\}^m\to\{0,1\}$ is **symmetric** when its value depends only on the number of ones in its input. A **symmetric circuit** has $m$ input bits (layer $0$), then $d$ layers of gates of arbitrary fan-in, and a list of output nodes. A gate lists its incoming wires, each from an input bit or a gate of a strictly earlier layer, together with a table
--   $$(t_0,\dots,t_f)\in\{0,1\}^{f+1},$$
--   where $f$ is the fan-in and the gate outputs $t_c$ when exactly $c$ of its incoming wires carry a one. Counts $c=0$ and $c=f$ are both included, and a gate of fan-in $0$ is a constant.
--
--   On input $x\in\{0,1\}^m$ the node values are computed layer by layer, and the circuit's output is the list of values at the output nodes. The size is
--   $$w \;=\; m+\sum_{g}(1+f_g)+(\text{number of outputs}),$$
--   which is within a constant factor of the number of gate-to-gate and input-to-gate wires when every input bit is read, every gate has an incoming wire, and no node is listed twice as an output.
--
--   The input tape holds a fixed binary encoding of $(C,x)$: a field width $L=\lfloor\log_2(w+d+2)\rfloor+1$ in unary, the numbers of inputs, layers and outputs in fields of $L$ bits, then $x$, then each layer as its number of gates followed by its gates (fan-in, references, table), and finally the outputs. Its length is $O(L(w+d))$.
--
--   These are the circuits of Theorem 1.1.
--
--   **Formalization Note** Wires are lists of node references, so a node may feed a gate more than once. The counted size includes one wire per input, gate and output so that unread inputs, constant gates and repeated outputs, which any evaluation must at least scan past, cannot make the size smaller than the input to be read.
-- source:
--   Adelmo Morrison Orozco, Nathan S. Sheffield, Ryan Williams, STOC 2027 submission #494 (October 2026), §2 "Symmetric circuits", printed p.7 (PDF p.8), and the hypotheses of Theorem 1.1, printed p.10 (PDF p.11)

import Mathlib
import Definitions.Def_CatalyticSorting494_Sorting_Machine

namespace CatalyticSorting494.Sorting

/-- A reference to a node: layer `0` holds the circuit's input bits and layer `ℓ + 1` holds the gates
of the `ℓ`-th entry of `SymCircuit.layers`. `index` is the position within the layer. -/
structure NodeRef where
  layer : ℕ
  index : ℕ

/-- A symmetric gate of arbitrary fan-in. `inputs` lists its incoming wires, and `table` lists its
output for each possible number of ones among the incoming wires. -/
structure SymGate where
  inputs : List NodeRef
  table : List Bool

/-- A circuit of symmetric gates with `numInputs` input bits, with its gates grouped in layers and a
list of output nodes. A gate may read the input bits and the gates of any earlier layer. -/
structure SymCircuit where
  numInputs : ℕ
  layers : List (List SymGate)
  outputs : List NodeRef

/-- The value at a node, given the values of all nodes computed so far. -/
def nodeValue (vals : List (List Bool)) (r : NodeRef) : Bool :=
  (vals.getD r.layer []).getD r.index false

/-- The gate's output: the table entry at the number of ones among its incoming wires. -/
def SymGate.eval (vals : List (List Bool)) (g : SymGate) : Bool :=
  g.table.getD ((g.inputs.map (nodeValue vals)).count true) false

namespace SymCircuit

/-- The number `d` of layers of gates. -/
def depth (C : SymCircuit) : ℕ := C.layers.length

/-- The number of nodes in a layer. -/
def layerSize (C : SymCircuit) : ℕ → ℕ
  | 0 => C.numInputs
  | ℓ + 1 => (C.layers.getD ℓ []).length

/-- `r` names an existing node in a layer below `bound`. -/
def ValidRef (C : SymCircuit) (bound : ℕ) (r : NodeRef) : Prop :=
  r.layer < bound ∧ r.index < C.layerSize r.layer

/-- A well-formed circuit: each gate's table has one entry per possible count `0, …, fan-in` of
ones; each wire comes from an existing node of a strictly earlier layer, which makes the circuit
acyclic; and each output names an existing node. -/
structure WellFormed (C : SymCircuit) : Prop where
  table_length : ∀ ℓ, ∀ g ∈ C.layers.getD ℓ [], g.table.length = g.inputs.length + 1
  input_valid : ∀ ℓ, ∀ g ∈ C.layers.getD ℓ [], ∀ r ∈ g.inputs, C.ValidRef (ℓ + 1) r
  output_valid : ∀ r ∈ C.outputs, C.ValidRef (C.depth + 1) r

/-- The values of all nodes on input `x`, layer by layer; entry `0` is `x`. -/
def allValues (C : SymCircuit) (x : List Bool) : List (List Bool) :=
  C.layers.foldl (fun vals layer => vals ++ [layer.map (SymGate.eval vals)]) [x]

/-- The circuit's output on input `x`. -/
def eval (C : SymCircuit) (x : List Bool) : List Bool :=
  C.outputs.map (nodeValue (C.allValues x))

/-- The size `w`: the incoming wires of all gates, plus one wire leaving each input bit, one leaving
each gate, and one for each output. When every input bit is read, every gate has an incoming wire
and no node is listed twice as an output, this is within a factor of five of the number of incoming
wires alone. -/
def wireCount (C : SymCircuit) : ℕ :=
  C.numInputs + (C.layers.map fun layer => (layer.map fun g => g.inputs.length + 1).sum).sum +
    C.outputs.length

/-- The width of the binary fields of the encoding, big enough for every count and index in a
well-formed circuit. -/
def fieldWidth (C : SymCircuit) : ℕ :=
  Nat.log 2 (C.wireCount + C.depth + 2) + 1

end SymCircuit

/-- A node reference as two binary fields of width `L`. -/
def NodeRef.bits (L : ℕ) (r : NodeRef) : List Bool :=
  natBits L r.layer ++ natBits L r.index

/-- A gate as its fan-in, its incoming wires, and its table. -/
def SymGate.bits (L : ℕ) (g : SymGate) : List Bool :=
  natBits L g.inputs.length ++ g.inputs.flatMap (NodeRef.bits L) ++ g.table

/-- The content of the input tape for circuit `C` on circuit input `x`: the field width in unary,
then the numbers of input bits, layers and outputs, then `x`, then each layer as its number of
gates and its gates, and finally the outputs. -/
def SymCircuit.encode (C : SymCircuit) (x : List Bool) : List Bool :=
  let L := C.fieldWidth
  List.replicate L true ++ [false] ++
    natBits L C.numInputs ++ natBits L C.depth ++ natBits L C.outputs.length ++ x ++
    C.layers.flatMap (fun layer => natBits L layer.length ++ layer.flatMap (SymGate.bits L)) ++
    C.outputs.flatMap (NodeRef.bits L)

end CatalyticSorting494.Sorting



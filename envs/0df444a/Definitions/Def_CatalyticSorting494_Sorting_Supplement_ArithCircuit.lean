-- Prove2me | Definitions.Def_CatalyticSorting494_Sorting_Supplement_ArithCircuit
-- name    : CatalyticSorting494_Sorting_Supplement_ArithCircuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:17:18.680193+00:00
-- url     : https://prove2.me/theorems/570eb8b4-27e6-46a8-a08c-166ea762d0eb
-- title:
--   Definition 4.1 — $\#\mathrm{NC}(K)$ arithmetic circuits, multiplicative depth, evaluation and input encoding
-- statement:
--   Let $R$ be a ring with $1$, not necessarily commutative. An **$\#\mathrm{NC}(R)$ circuit** has input wires and gates of the following kinds: fan-in 2 addition gates $u+v$, fan-in 2 product gates $u\cdot v$, and, for each constant $x\in R$, fan-in 1 gates $u\mapsto u\times x$ and $u\mapsto u+x$. Since $R$ need not be commutative, the constant multiplication is provided on both sides, $u\mapsto u\,x$ and $u\mapsto x\,u$; in a commutative ring they are the same gate. The gates are presented grouped into layers $1,\dots,\ell$, layer $0$ being the input wires, and each gate reads only nodes of strictly earlier layers. The **multiplicative depth** of the circuit is
--
--   $$d=\#\{\text{layers containing at least one fan-in 2 product gate}\},$$
--
--   so any number of purely linear layers ($+$, $\times x$, $+x$) between product layers is free. Given values $x_1,\dots,x_m\in R$ of the input wires, every gate gets a value in $R$ layer by layer, and the **output** of the circuit is the list of values of its designated output nodes. The number $w$ of **wires** counts the incoming wires of all gates plus one wire leaving each input, each gate and each output.
--
--   To be the input of an algorithm, a circuit over $K_n$ is written on the input tape as: $1^n$ and a separator, a field width $F$ in unary, the numbers of inputs, layers and outputs in binary fields of width $F$, the codes $e_n(x_1),\dots,e_n(x_m)$ of the input values, every layer as its number of gates followed by its gates (a three-bit type tag, the incoming wires as (layer, position) pairs, and for a $\times x$ or $+x$ gate the code $e_n(x)$), and finally the output nodes. Nothing about the circuit, its constants included, is available other than through this encoding.
--
--   This is the circuit class of Theorem 4.3.
--
--   **Formalization Note** Wires are the published `NodeRef` of the base mission's symmetric circuits, and the wire count follows the same convention as the published `SymCircuit.wireCount`. A gate reading a missing node reads $0$; `WellFormed` excludes this. The encoding takes the code map $e_n$ as a parameter, so it is the same as Definition 4.2's encoding of ring elements.
-- source:
--   Adelmo Morrison Orozco, Nathan S. Sheffield, Ryan Williams, STOC 2027 submission #494 (October 2026), Definition 4.1, printed p.14 (PDF p.15); wire/layer conventions as in §3.1

import Mathlib
import Definitions.Def_CatalyticSorting494_Sorting_Machine
import Definitions.Def_CatalyticSorting494_Sorting_SymCircuit

namespace CatalyticSorting494.Sorting.Supplement

open CatalyticSorting494.Sorting

/-- A gate of an `#NC(R)` circuit (Definition 4.1): a fan-in 2 addition gate, a fan-in 2 product
gate, or a fan-in 1 gate `×x` or `+x` for a constant `x ∈ R`. The ring need not be commutative, so
`×x` is provided both as right multiplication `u ↦ u * x` (`mulConst`) and as left multiplication
`u ↦ x * u` (`constMul`); in a commutative ring the two coincide. Wires are `NodeRef`s: layer `0` holds
the circuit's input wires and layer `ℓ + 1` the gates of the `ℓ`-th layer. -/
inductive ArithGate (R : Type*) where
  | add (a b : NodeRef)
  | mul (a b : NodeRef)
  | mulConst (x : R) (a : NodeRef)
  | constMul (x : R) (a : NodeRef)
  | addConst (x : R) (a : NodeRef)

/-- The value at a node, given the values of all nodes computed so far. -/
def arithNodeValue {R : Type*} [Zero R] (vals : List (List R)) (r : NodeRef) : R :=
  (vals.getD r.layer []).getD r.index 0

namespace ArithGate

variable {R : Type*}

/-- The incoming wires of a gate. -/
def inputs : ArithGate R → List NodeRef
  | add a b => [a, b]
  | mul a b => [a, b]
  | mulConst _ a => [a]
  | constMul _ a => [a]
  | addConst _ a => [a]

/-- Whether the gate is a fan-in 2 product gate. -/
def isProduct : ArithGate R → Bool
  | mul _ _ => true
  | _ => false

/-- The gate's value in `R`, given the values of the nodes of earlier layers. -/
def eval [Ring R] (vals : List (List R)) : ArithGate R → R
  | add a b => arithNodeValue vals a + arithNodeValue vals b
  | mul a b => arithNodeValue vals a * arithNodeValue vals b
  | mulConst x a => arithNodeValue vals a * x
  | constMul x a => x * arithNodeValue vals a
  | addConst x a => arithNodeValue vals a + x

/-- A gate as a three-bit type tag, its incoming wires (each as two fields of width `L`), and for a
`×x` (either side) or `+x` gate the code of the constant `x`. -/
def bits (L : ℕ) (code : R → List Bool) : ArithGate R → List Bool
  | add a b => natBits 3 0 ++ NodeRef.bits L a ++ NodeRef.bits L b
  | mul a b => natBits 3 1 ++ NodeRef.bits L a ++ NodeRef.bits L b
  | mulConst x a => natBits 3 2 ++ NodeRef.bits L a ++ code x
  | addConst x a => natBits 3 3 ++ NodeRef.bits L a ++ code x
  | constMul x a => natBits 3 4 ++ NodeRef.bits L a ++ code x

end ArithGate

/-- An `#NC(R)` circuit (Definition 4.1) with `numInputs` input wires, its gates grouped in layers,
and a list of output nodes. A gate may read input wires and gates of any earlier layer. -/
structure ArithCircuit (R : Type*) where
  numInputs : ℕ
  layers : List (List (ArithGate R))
  outputs : List NodeRef

namespace ArithCircuit

variable {R : Type*}

/-- The multiplicative depth `d`: the number of layers containing at least one fan-in 2 product
gate. Layers of additions and constant gates are not counted. -/
def multDepth (C : ArithCircuit R) : ℕ :=
  C.layers.countP fun layer => layer.any ArithGate.isProduct

/-- The number of nodes in a layer. -/
def layerSize (C : ArithCircuit R) : ℕ → ℕ
  | 0 => C.numInputs
  | ℓ + 1 => (C.layers.getD ℓ []).length

/-- `r` names an existing node in a layer below `bound`. -/
def ValidRef (C : ArithCircuit R) (bound : ℕ) (r : NodeRef) : Prop :=
  r.layer < bound ∧ r.index < C.layerSize r.layer

/-- A well-formed circuit: every wire comes from an existing node of a strictly earlier layer (so
the circuit is acyclic and layered as in Definition 4.1), and every output names an existing node. -/
structure WellFormed (C : ArithCircuit R) : Prop where
  input_valid : ∀ ℓ, ∀ g ∈ C.layers.getD ℓ [], ∀ r ∈ g.inputs, C.ValidRef (ℓ + 1) r
  output_valid : ∀ r ∈ C.outputs, C.ValidRef (C.layers.length + 1) r

/-- The values of all nodes on the input assignment `x`, layer by layer; entry `0` is `x`. -/
def allValues [Ring R] (C : ArithCircuit R) (x : List R) : List (List R) :=
  C.layers.foldl (fun vals layer => vals ++ [layer.map (ArithGate.eval vals)]) [x]

/-- The values of the circuit's output wires on input assignment `x`. -/
def eval [Ring R] (C : ArithCircuit R) (x : List R) : List R :=
  C.outputs.map (arithNodeValue (C.allValues x))

/-- The number `w` of wires: the incoming wires of all gates, plus one wire leaving each input,
one leaving each gate, and one for each output (the convention of the published `SymCircuit`). -/
def wireCount (C : ArithCircuit R) : ℕ :=
  C.numInputs + (C.layers.map fun layer => (layer.map fun g => g.inputs.length + 1).sum).sum +
    C.outputs.length

/-- The width of the binary fields of the encoding, big enough for every count and index in a
well-formed circuit. -/
def fieldWidth (C : ArithCircuit R) : ℕ :=
  Nat.log 2 (C.wireCount + C.layers.length + 2) + 1

/-- The content of the input tape for circuit `C` over `K_n` on input assignment `x`, where `code`
is the ring encoding `e_n`: the index `n` in unary, then the field width in unary, then the numbers
of inputs, layers and outputs, then the codes of the input values, then each layer as its number of
gates and its gates (constants as their codes), and finally the outputs. -/
def encode (code : R → List Bool) (n : ℕ) (C : ArithCircuit R) (x : List R) : List Bool :=
  let L := C.fieldWidth
  List.replicate n true ++ [false] ++ List.replicate L true ++ [false] ++
    natBits L C.numInputs ++ natBits L C.layers.length ++ natBits L C.outputs.length ++
    x.flatMap code ++
    C.layers.flatMap (fun layer => natBits L layer.length ++ layer.flatMap (ArithGate.bits L code)) ++
    C.outputs.flatMap (NodeRef.bits L)

end ArithCircuit

end CatalyticSorting494.Sorting.Supplement



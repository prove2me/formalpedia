-- Prove2me | Definitions.Def_PrivPCP_Supplement_LCircuit
-- name    : PrivPCP_Supplement_LCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:52:34.202303+00:00
-- url     : https://prove2.me/theorems/45c1af32-a035-4608-8a1b-4f86b1f6ab15
-- title:
--   Layered computation circuits with auxiliary and random words (Definition 5.3, circuit part)
-- statement:
--   An **$L$-layer computation circuit with auxiliary proofs** over $\mathbb F_q$ has an input of length $N_0$ and layers $1,\dots,L$. Layer $\ell$ receives the **input block** $(W_{\ell-1},\Pi_\ell,R_\ell)$: the current state $W_{\ell-1}$ ($W_0$ is the input), auxiliary words $\Pi_\ell$ supplied by an external prover, and fresh random words $R_\ell$. Its **computation gates** each read at most $\Delta$ wires of this block and output one field element; their outputs form the next state $W_\ell$. The final state $W_L$ is a single wire, the output.
--
--   1. A gate's operation is a **local program**: a Turing machine with a parameter string and a step budget, run on the values it reads (written in binary); its output, read as a binary number, is reduced mod $q$.
--   2. The **transcript coordinates** are the input, auxiliary, random-input and computation-output wires.
--   3. An execution in which every gate outside a set $E$ evaluates correctly on its actual inputs is an execution with faulty set $E$; it is **$\varepsilon$-faulty** if in every layer fewer than an $\varepsilon$-fraction of the gates are faulty (in particular, the fault-free execution is $\varepsilon$-faulty for every $\varepsilon$).
--   4. The **description** of a circuit is the bit string listing $N_0$ and, for every layer, its block lengths and its gates (wires read and program).
--
--   This is the circuit model of Theorem 5.5; the tester, the honest execution, the measure $\mu$ and the privacy and robustness clauses are separate definitions built on it.
--
--   **Formalization Note** Wires inside a block are numbered by natural numbers: $(0,j)$ is position $j$ of the state, $(1,j)$ of the auxiliary words, $(2,j)$ of the random words. Well-formedness requires at least one layer, every read wire to exist, and a last layer with exactly one gate. Definition 5.3 does not name the gate operations; the gates of §5.3 decode Reed–Solomon lines up to half the minimum distance, which no short list of monomials computes, so a gate's operation is a short program, which makes "the description can be constructed in polynomial time" meaningful.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Definition 5.3, pp.27–28 (PDF pp.29–30)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_OTM_code
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_ZKSheafPCP_queryLog

set_option autoImplicit false

open QAlgorithms.Complexity QAdvFew.PoQOracle ZKSheafPCP

namespace PrivPCP.Supplement

/-- A **local program**: an oracle Turing machine `prog` (run with the empty oracle), a parameter
string `param` and a step budget `budget` (Bafna, Vyas, *Private PCPs from Product Expansion*, STOC
2027 submission manuscript (sha256 c2cac1e0…), Definition 5.3, p.27: the operation of a gate, and the
decision of a tester, on the values they read). On a list of field values `v₁, …, v_m` it runs `prog`
on `(param, v₁, …, v_m)` (each `v_j` as the binary numeral of its representative in `{0, …, q−1}`)
for `budget` steps.

**Formalization Note** Definition 5.3 does not name the gate operations. A description that can be
constructed in polynomial time must describe each gate by a short program; §5.3's gates decode
Reed–Solomon lines up to half the minimum distance, which no short list of monomials computes, so
the operation of a gate is a machine with a parameter string (for example the line and the
constraint it handles) and a step budget. -/
structure LocalProg where
  /-- the machine -/
  prog : OTM
  /-- the parameter string -/
  param : Str
  /-- the step budget -/
  budget : ℕ

/-- The number written by a bit string in binary, least significant bit first (the inverse of
`binN`). -/
def bitsVal (l : Str) : ℕ := l.foldr (fun b n => 2 * n + cond b 1 0) 0

namespace LocalProg

/-- The input of a local program on the values `v`. -/
def input {q : ℕ} (p : LocalProg) (v : List (ZMod q)) : Str :=
  tup [p.param, tup (v.map fun a => binN a.val)]

/-- The field value a local program computes: the work-tape contents after `budget` steps, read as a
binary number and reduced mod `q`. -/
def evalField {q : ℕ} (p : LocalProg) (v : List (ZMod q)) : ZMod q :=
  ((bitsVal (p.prog.output (fun _ => false) (p.input v) p.budget) : ℕ) : ZMod q)

/-- A local program **accepts** the values `v` if it has accepted within `budget` steps. -/
def Accepts {q : ℕ} (p : LocalProg) (v : List (ZMod q)) : Prop :=
  p.prog.result (fun _ => false) (p.input v) p.budget = some true

/-- The description of a local program. -/
def code (p : LocalProg) : Str := tup [p.prog.code, p.param, binN p.budget]

end LocalProg

/-- A **computation gate** of a layer: the list of wires it reads from the layer's input block
`(W_{ℓ−1}, Π_ℓ, R_ℓ)` and its operation. A wire `(0, j)` is position `j` of the state `W_{ℓ−1}`,
`(1, j)` position `j` of the auxiliary words `Π_ℓ`, `(2, j)` position `j` of the random words `R_ℓ`.
Its fan-in is the length of `ins`. -/
structure Gate where
  /-- the wires read, in order -/
  ins : List (Fin 3 × ℕ)
  /-- the operation -/
  op : LocalProg

/-- A **layer**: the lengths of its auxiliary block `Π_ℓ` and random block `R_ℓ`, and its computation
gates, whose outputs form the next state `W_ℓ`. -/
structure Layer where
  /-- length of `Π_ℓ` -/
  auxLen : ℕ
  /-- length of `R_ℓ` -/
  rndLen : ℕ
  /-- the computation gates -/
  gates : List Gate

/-- An `L`-layer **computation circuit with auxiliary proofs** (Definition 5.3, p.27): the input length
`N₀` and the list of layers. Layer `ℓ` (`0`-indexed here; the paper's layer `ℓ + 1`) reads the input
block `(W_ℓ, Π_{ℓ+1}, R_{ℓ+1})`, where `W_0` is the input, and its gates produce the next state.

**Formalization Note** Wires are numbered by natural numbers inside each block; well-formedness
(`WF`) says every wire a gate reads exists and that the last state is a single wire (the output
`W_L`). -/
structure LCircuit where
  /-- the input length `N₀` -/
  N0 : ℕ
  /-- the layers, in order -/
  layers : List Layer

namespace LCircuit

variable (C : LCircuit)

/-- The number `L` of layers (the depth). -/
def L : ℕ := C.layers.length

/-- Layer `ℓ`. -/
def layer (ℓ : Fin C.L) : Layer := C.layers.get ℓ

/-- Indices of the auxiliary wires of all layers. -/
abbrev AuxIdx : Type := Σ ℓ : Fin C.L, Fin (C.layer ℓ).auxLen
/-- Indices of the random-input wires of all layers. -/
abbrev RndIdx : Type := Σ ℓ : Fin C.L, Fin (C.layer ℓ).rndLen
/-- Indices of the computation gates (computation-output wires) of all layers. -/
abbrev OutIdx : Type := Σ ℓ : Fin C.L, Fin (C.layer ℓ).gates.length

/-- The **transcript coordinates**: input, auxiliary, random-input and computation-output wires
(Definition 5.3(2b), p.28). -/
abbrev Coord : Type := Fin C.N0 ⊕ C.AuxIdx ⊕ C.RndIdx ⊕ C.OutIdx

/-- The coordinate of a computation-output wire. -/
def outC (o : C.OutIdx) : C.Coord := Sum.inr (Sum.inr (Sum.inr o))

/-- The coordinate of the block wire `w` of layer `ℓ`, if it exists: `(0, j)` is position `j` of the
input (layer `0`) or of the outputs of layer `ℓ − 1`; `(1, j)` and `(2, j)` are positions of this
layer's auxiliary and random words. -/
def blockCoord (ℓ : Fin C.L) (w : Fin 3 × ℕ) : Option C.Coord :=
  if w.1 = 0 then
    if hℓ : (ℓ : ℕ) = 0 then
      (if h : w.2 < C.N0 then some (Sum.inl ⟨w.2, h⟩) else none)
    else
      let ℓ' : Fin C.L := ⟨ℓ - 1, by omega⟩
      if h : w.2 < (C.layer ℓ').gates.length then some (C.outC ⟨ℓ', ⟨w.2, h⟩⟩) else none
  else if w.1 = 1 then
    (if h : w.2 < (C.layer ℓ).auxLen then some (Sum.inr (Sum.inl ⟨ℓ, ⟨w.2, h⟩⟩)) else none)
  else
    (if h : w.2 < (C.layer ℓ).rndLen then some (Sum.inr (Sum.inr (Sum.inl ⟨ℓ, ⟨w.2, h⟩⟩))) else none)

/-- The input block `(W_{ℓ−1}, Π_ℓ, R_ℓ)` of layer `ℓ` as a set of transcript coordinates. -/
def blockSet (ℓ : Fin C.L) : Set C.Coord := {c | ∃ w, C.blockCoord ℓ w = some c}

/-- The value of block wire `w` of layer `ℓ` in a transcript (`0` for a wire that does not exist,
which a well-formed circuit never reads). -/
def blockVal {q : ℕ} (t : C.Coord → ZMod q) (ℓ : Fin C.L) (w : Fin 3 × ℕ) : ZMod q :=
  match C.blockCoord ℓ w with
  | some c => t c
  | none => 0

/-- The gate `o`. -/
def gate (o : C.OutIdx) : Gate := (C.layer o.1).gates.get o.2

/-- The value gate `o` computes from its actual inputs in the transcript `t`. -/
def gateVal {q : ℕ} (t : C.Coord → ZMod q) (o : C.OutIdx) : ZMod q :=
  (C.gate o).op.evalField ((C.gate o).ins.map (C.blockVal t o.1))

/-- The transcript `t` is an execution in which every computation gate outside `E` evaluates
correctly on its actual inputs (Definition 5.3(3), p.28); the gates in `E` are the faulty ones, whose
outputs are arbitrary. With `E = ∅` this is a fault-free execution. -/
def Computes {q : ℕ} (E : Set C.OutIdx) (t : C.Coord → ZMod q) : Prop :=
  ∀ o, o ∉ E → t (C.outC o) = C.gateVal t o

/-- The faulty set `E` changes fewer than an `ε`-fraction of the computation gates in each layer
(no gate of a layer is faulty, or fewer than `ε · |layer|` are). -/
def FewFaults (ε : ℝ) (E : Set C.OutIdx) : Prop :=
  ∀ ℓ : Fin C.L, {o ∈ E | o.1 = ℓ}.ncard = 0 ∨
    ({o ∈ E | o.1 = ℓ}.ncard : ℝ) < ε * (C.layer ℓ).gates.length

/-- The coordinate of the final output wire `W_L` (the first gate of the last layer), if it exists. -/
def finalCoord : Option C.Coord :=
  if h : 0 < C.L then
    if h1 : 0 < (C.layer ⟨C.L - 1, by omega⟩).gates.length then
      some (C.outC ⟨⟨C.L - 1, by omega⟩, ⟨0, h1⟩⟩)
    else none
  else none

/-- The circuit output `W_L` in a transcript. -/
def outVal {q : ℕ} (t : C.Coord → ZMod q) : ZMod q :=
  match C.finalCoord with
  | some c => t c
  | none => 0

/-- **Well-formedness**: there is at least one layer, every wire a gate reads exists in its layer's
input block, and the last layer has exactly one gate, the output `W_L`. -/
def WF : Prop :=
  0 < C.L ∧
  (∀ (ℓ : Fin C.L), ∀ g ∈ (C.layer ℓ).gates, ∀ w ∈ g.ins, (C.blockCoord ℓ w).isSome) ∧
  ∀ h : 0 < C.L, (C.layer ⟨C.L - 1, by omega⟩).gates.length = 1

/-- The total number of computation gates. -/
def gateCount : ℕ := (C.layers.map fun l => l.gates.length).sum

/-- The **description** of a circuit: `N₀`, then every layer (its block lengths and its gates, each
with its wires and its program). -/
def code : Str :=
  tup [binN C.N0, tup (C.layers.map fun l =>
    tup [binN l.auxLen, binN l.rndLen, tup (l.gates.map fun g =>
      tup [tup (g.ins.map fun w => tup [binN w.1.val, binN w.2]), g.op.code])])]

end LCircuit

end PrivPCP.Supplement



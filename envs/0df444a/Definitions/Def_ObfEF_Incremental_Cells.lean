-- Prove2me | Definitions.Def_ObfEF_Incremental_Cells
-- name    : ObfEF_Incremental_Cells
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:56:08.016127+00:00
-- url     : https://prove2.me/theorems/3888f45c-bf7f-450a-83a6-4da9b370a683
-- title:
--   Cells, configurations and proper configurations of the topology U_{il,ol,M} (Definition 3.3)
-- statement:
--   Let $il,ol,M\ge1$. The topology $U_{il,ol,M}$ (Definition 3.3) has input wires $w_1,\dots,w_{il}$, $M$ **cells** and $ol$ outputs.
--
--   1. Cell $j\in[M]$ has the constant gates $c^\beta_{j,i}$ ($\beta\in\{0,1\}$, $i\in[il+j-1]$) and $e^1_j,\dots,e^4_j$, and the gates
--   $$a^\beta_j=\bigvee_{i\in[il+j-1]}\big(c^\beta_{j,i}\wedge w_i\big),\qquad w_{il+j}=\Big(\big(e^1_j\wedge(a^0_j\wedge a^1_j)\big)\vee\big(e^2_j\wedge(a^0_j\vee a^1_j)\big)\Big)\vee\Big(\big(e^3_j\wedge\neg a^0_j\big)\vee e^4_j\Big),$$
--   where a disjunction is a left-nested chain of $\vee$ gates and $c^\beta_{j,i}\wedge w_i$ is a **product**. The wire $w_{il+j}$ is the output of cell $j$.
--   2. Output $k\in[ol]$ is $o_k=\bigvee_{i\in[il+M]}(d_{k,i}\wedge w_i)$ with constant gates $d_{k,i}$.
--   3. A **configuration** assigns bits to the constant gates; it is identified with the resulting circuit. All configurations share one topology: each constant gate reads the first input wire.
--   4. A configuration is **proper** if every output $k$ has a unique constant $d_{k,i}$ labelled $1$ (output $k$ then **selects** $w_i$) and the constants labelled $1$ in every cell have one of four forms: none (instruction $0$, the cell is **inactive**); only $e^4_j$ (instruction $1$); $e^3_j$ and one $c^0_{j,i}$ (instruction $\neg w_i$); $e^1_j$ or $e^2_j$ with one $c^0_{j,i}$ and one $c^1_{j,i'}$ (instruction $w_i\wedge w_{i'}$ or $w_i\vee w_{i'}$). A cell **selects** the wires of its instruction.
--
--   When the instructions of a set $J$ of cells change, $\hat w_j$ denotes the function computed by cell $j\in J$ when the cells of $J$ are evaluated in order and the values of the other wires they select are treated as independent inputs (p. 47).
--
--   This universal topology lets an instruction change by relabelling constants only, without adding or removing a wire.
--
--   **Formalization Note.** Indices are 0-based: $w_i$ for $i<il$ is input wire $i$, $w_{il+j}$ is the output of cell $j<M$. `U il ol M` is the `Wiring` produced by the builder `UBuild` (cells in order, then the output selectors; inside a cell the selector of $a^0$, that of $a^1$, $e^1,\dots,e^4$, then the nine gates in the order of the displayed formula; each product $c\wedge w$ reads $c$ first; a NOT gate reads its operand and wire $0$). `labels il ol M cfg` are the gate functions of configuration `cfg : CName → Bool`. A proper configuration is given by instruction data `Prog` (an `Instr` per cell, a selected index per output): `IsProper` says that the configuration agrees on the constants of $U$ with `p.toConfig` for valid data `p`. `hatW il M p J j ρ` is $\hat w_j$, with `ρ` the values of all wires outside the outputs of $J$.
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), pp. 46-47, Definition 3.3 and 'Changing a Few Instructions'

import Mathlib
import Definitions.Def_ObfEF_Incremental_GateList

/-!
# Cells, configurations and proper configurations: the topology `U_{il,ol,M}` (Definition 3.3)

Abram, Datta, Dutta, Roy, *Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to
Falsifiable Assumptions*, STOC 2027 submission (manuscript sha256 f9518747…), pp. 46–47,
Definition 3.3, and p. 47 ("Changing a Few Instructions": the functions `ŵ_j`).

Indexing (0-based). The wires `w_0, …, w_{il+M-1}` of the paper's `w_1, …, w_{il+M}`: `w_i` for
`i < il` is input wire `i`, and `w_{il+j}` is the output of cell `j < M`. Cell `j` has the constant
gates `c^β_{j,i}` (`β ∈ {0,1}`, `i < il + j`) and `e^1_j, …, e^4_j`, the gates
`a^β_j = ⋁_{i < il+j} (c^β_{j,i} ∧ w_i)` (a left-nested chain of `∨` over the products) and
`w_{il+j} = ((e¹ ∧ (a⁰ ∧ a¹)) ∨ (e² ∧ (a⁰ ∨ a¹))) ∨ ((e³ ∧ ¬a⁰) ∨ e⁴)`. Output `k < ol` is
`⋁_{i < il+M} (d_{k,i} ∧ w_i)`.

Gate-list conventions (§2.1.1, p. 47): every constant gate reads the first input wire (wire `0`)
as both arguments, a `NOT` gate reads its operand and wire `0`, and a product `c ∧ w` reads `c`
first. The gates are emitted in a topological order by the builder below. A configuration assigns
a bit to every constant name; the circuit `D` of a configuration is the wiring `U il ol M` with the
gate functions `labels il ol M cfg`.
-/

namespace ObfEF.Incremental

/-- Names of the constant gates of `U_{il,ol,M}`: `c β j i` is `c^β_{j,i}`, `e m j` is `e^m_j`
(`m ∈ {1,2,3,4}`), `d k i` is `d_{k,i}`. -/
inductive CName where
  | c (β : Bool) (j i : ℕ)
  | e (m j : ℕ)
  | d (k i : ℕ)
  deriving DecidableEq

/-- The kind of a gate of `U`: a named constant or one of the fixed operations. -/
inductive UKind where
  | const (c : CName)
  | and
  | or
  | not
  deriving DecidableEq

/-- A gate of `U`: its kind and its two input wires. -/
structure UGate where
  kind : UKind
  l : ℕ
  r : ℕ

namespace UBuild

/-- Gates emitted so far (gate `j` writes wire `il + j`). -/
abbrev B := StateM (Array UGate)

/-- Emit a gate and return its output wire. -/
def emit (il : ℕ) (g : UGate) : B ℕ := modifyGet fun a => (il + a.size, a.push g)

/-- A constant gate; it reads the first input wire. -/
def constG (il : ℕ) (c : CName) : B ℕ := emit il ⟨.const c, 0, 0⟩
def andG (il a b : ℕ) : B ℕ := emit il ⟨.and, a, b⟩
def orG (il a b : ℕ) : B ℕ := emit il ⟨.or, a, b⟩
/-- A `NOT` gate; its missing second argument is the first input wire. -/
def notG (il a : ℕ) : B ℕ := emit il ⟨.not, a, 0⟩

/-- `⋁_i (c_i ∧ w_i)` over the wires `ws` (index `i` counted from `i₀`), left-nested; `acc` is the
disjunction built so far. -/
def selectorAux (il : ℕ) (name : ℕ → CName) : ℕ → Option ℕ → List ℕ → B ℕ
  | _, acc, [] => pure (acc.getD 0)
  | i, acc, w :: ws => do
      let c ← constG il (name i)
      let p ← andG il c w
      let acc' ← match acc with
        | none => pure p
        | some a => orG il a p
      selectorAux il name (i + 1) (some acc') ws

/-- The selector `⋁_{i} (name(i) ∧ w_i)` over the wires `ws = (w_0, w_1, …)`. -/
def selector (il : ℕ) (name : ℕ → CName) (ws : List ℕ) : B ℕ :=
  selectorAux il name 0 none ws

/-- Cell `j`, reading the wires `ws = (w_0, …, w_{il+j-1})`; returns its output wire `w_{il+j}`. -/
def cell (il j : ℕ) (ws : List ℕ) : B ℕ := do
  let a0 ← selector il (CName.c false j) ws
  let a1 ← selector il (CName.c true j) ws
  let e1 ← constG il (.e 1 j)
  let e2 ← constG il (.e 2 j)
  let e3 ← constG il (.e 3 j)
  let e4 ← constG il (.e 4 j)
  let g1 ← andG il a0 a1
  let g2 ← andG il e1 g1
  let g3 ← orG il a0 a1
  let g4 ← andG il e2 g3
  let g5 ← orG il g2 g4
  let g6 ← notG il a0
  let g7 ← andG il e3 g6
  let g8 ← orG il g7 e4
  orG il g5 g8

/-- Cells `j, j+1, …, j+m-1`; returns the extended list of `w` wires. -/
def cells (il : ℕ) : ℕ → List ℕ → ℕ → B (List ℕ)
  | _, ws, 0 => pure ws
  | j, ws, m + 1 => do
      let w ← cell il j ws
      cells il (j + 1) (ws ++ [w]) m

/-- The whole topology: the `M` cells, then the `ol` output selectors. Returns the wires of
`w_0, …, w_{il+M-1}` and the output wires. -/
def build (il ol M : ℕ) : B (List ℕ × List ℕ) := do
  let ws ← cells il 0 (List.range il) M
  let outs ← (List.range ol).mapM fun k => selector il (CName.d k) ws
  pure (ws, outs)

/-- The result of the builder: (gates, w wires, output wires). -/
def result (il ol M : ℕ) : (List ℕ × List ℕ) × Array UGate := (build il ol M).run #[]

end UBuild

/-- The gates of `U_{il,ol,M}` in topological order. -/
def Ugates (il ol M : ℕ) : Array UGate := (UBuild.result il ol M).2

/-- The wire of `w_i` (`i < il + M`) in `U_{il,ol,M}`. -/
def Uw (il ol M i : ℕ) : ℕ := (UBuild.result il ol M).1.1.getD i 0

/-- The topology `U_{il,ol,M}` in the gate-list view. -/
def U (il ol M : ℕ) : Wiring where
  il := il
  n := (Ugates il ol M).size
  ol := ol
  l j := ((Ugates il ol M)[j]).l
  r j := ((Ugates il ol M)[j]).r
  out k := (UBuild.result il ol M).1.2.getD k 0

/-- A configuration: a bit for every constant gate. -/
abbrev Config := CName → Bool

/-- The gate functions of the circuit of configuration `cfg`: a constant gate outputs its bit, the
other gates keep their operation in every configuration. -/
def labels (il ol M : ℕ) (cfg : Config) : Fin (U il ol M).n → Bool → Bool → Bool :=
  fun j =>
    match ((Ugates il ol M)[j]).kind with
    | .const c => fun _ _ => cfg c
    | .and => fun a b => a && b
    | .or => fun a b => a || b
    | .not => fun a _ => !a

/-- The instruction of a cell in a proper configuration, with operands given as `w`-indices:
`0`, `1`, `¬w_i`, `w_i ∧ w_{i'}`, `w_i ∨ w_{i'}`. -/
inductive Instr where
  | zero
  | one
  | neg (i : ℕ)
  | and (i i' : ℕ)
  | or (i i' : ℕ)
  deriving DecidableEq

namespace Instr

/-- The `w`-indices a cell with this instruction selects. -/
def selects : Instr → Finset ℕ
  | zero => ∅
  | one => ∅
  | neg i => {i}
  | and i i' => {i, i'}
  | or i i' => {i, i'}

/-- Value of the instruction when `w_i` has value `v i`. -/
def eval (v : ℕ → Bool) : Instr → Bool
  | zero => false
  | one => true
  | neg i => !v i
  | and i i' => v i && v i'
  | or i i' => v i || v i'

/-- The constants of cell `j` labelled 1 by the instruction (the four forms of Definition 3.3). -/
def constBit (j : ℕ) (ins : Instr) : CName → Bool
  | .c β j' i =>
      decide (j' = j) &&
        match ins with
        | neg a => !β && decide (i = a)
        | and a a' => (!β && decide (i = a)) || (β && decide (i = a'))
        | or a a' => (!β && decide (i = a)) || (β && decide (i = a'))
        | _ => false
  | .e m j' =>
      decide (j' = j) &&
        match ins with
        | one => decide (m = 4)
        | neg _ => decide (m = 3)
        | and _ _ => decide (m = 1)
        | or _ _ => decide (m = 2)
        | zero => false
  | .d _ _ => false

end Instr

/-- A proper configuration given by its data: the instruction of every cell and the `w`-index
selected by every output. -/
structure Prog where
  instr : ℕ → Instr
  sel : ℕ → ℕ

namespace Prog

/-- Operands of cell `j` are earlier wires `w_i`, `i < il + j`; outputs select one of the
`il + M` wires. -/
def Valid (il ol M : ℕ) (p : Prog) : Prop :=
  (∀ j < M, ∀ i ∈ (p.instr j).selects, i < il + j) ∧ (∀ k < ol, p.sel k < il + M)

/-- The configuration of `p`: the constants labelled 1 are those of the instruction forms of the
cells, and `d_{k,i} = 1` exactly for `i = sel k`. -/
def toConfig (p : Prog) : Config
  | .c β j i => (p.instr j).constBit j (.c β j i)
  | .e m j => (p.instr j).constBit j (.e m j)
  | .d k i => decide (p.sel k = i)

end Prog

/-- The constant names present in `U_{il,ol,M}`. -/
def IsUConst (il ol M : ℕ) : CName → Prop
  | .c _ j i => j < M ∧ i < il + j
  | .e m j => j < M ∧ 1 ≤ m ∧ m ≤ 4
  | .d k i => k < ol ∧ i < il + M

/-- `cfg` is a proper configuration: every output has a unique constant `d_{k,i}` labelled 1 and
every cell has one of the four instruction forms; equivalently, on the constants of `U` it agrees
with the configuration of valid instruction data. -/
def IsProper (il ol M : ℕ) (cfg : Config) : Prop :=
  ∃ p : Prog, p.Valid il ol M ∧ ∀ c, IsUConst il ol M c → cfg c = p.toConfig c

/-- `ŵ`: evaluate the cells of `J` in their order, treating the values `ρ` at all other wires as
independent inputs; `hatVals … M (il + j)` is `ŵ_j(ρ)` for `j ∈ J`. -/
def hatVals (il : ℕ) (p : Prog) (J : Finset ℕ) (ρ : ℕ → Bool) : ℕ → ℕ → Bool
  | 0 => ρ
  | j + 1 =>
      if j ∈ J then
        Function.update (hatVals il p J ρ j) (il + j) ((p.instr j).eval (hatVals il p J ρ j))
      else hatVals il p J ρ j

/-- The function `ŵ_j : {0,1}^R → {0,1}` computed by cell `j ∈ J` (the values of the wires
outside the outputs of `J` are given by `ρ`). -/
def hatW (il M : ℕ) (p : Prog) (J : Finset ℕ) (j : ℕ) (ρ : ℕ → Bool) : Bool :=
  hatVals il p J ρ M (il + j)

end ObfEF.Incremental



-- Prove2me | Definitions.Def_CatalyticSorting494_Sorting_Machine
-- name    : CatalyticSorting494_Sorting_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:41.691055+00:00
-- url     : https://prove2.me/theorems/9a871e9f-60b3-4646-ba61-eafca8ab75d7
-- title:
--   Random-access Turing machines with clean and catalytic tapes, and the dirty-XOR-output model
-- statement:
--   A **catalytic machine** has a read-only input tape $x$, a clean work tape that starts all zero, and a catalytic (dirty) work tape $z\in\{0,1\}^{c}$ of fixed length $c$ with arbitrary initial content. All three are accessed at random: each has a one-sided binary **index tape** with a sequential head, and the machine reads (and, on the two work tapes, writes) the cell whose address is written on that index tape, least significant bit first.
--
--   The program is a finite control with a transition table. In one step of unit cost it sees six bits, namely the bit under each index head and the three addressed cells. It then writes a bit under each index head and moves each of them by at most one cell, writes the addressed clean and catalytic cells, and changes state, or else it halts. The input and catalytic tapes read as $0$ past their ends, and a catalytic write past the end has no effect.
--
--   The clean space of a run counts the clean cells addressed plus every visited cell of the three index tapes, so all addresses are charged as clean bits. A machine **computes** $\mathrm{out}$ on $(x,z)$ within time $T$ and clean space $S$ when $|\mathrm{out}|\le |z|$ and the run from $z$ halts after at most $T$ steps, with clean space at most $S$, and with final catalytic content
--   $$\big(z_1\oplus \mathrm{out}_1,\ \dots,\ z_k\oplus \mathrm{out}_k,\ z_{k+1},\ \dots,\ z_c\big),\qquad k=|\mathrm{out}|.$$
--
--   This is the dirty-XOR-output model of Definition 2.2, on which every statement of the mission rests. A machine has no arithmetic or comparison primitive, and it has no parameter that depends on the instance. The file also fixes the binary field encoding of numbers and the bound $A\,T(\log_2(T+2))^k$ used for $\tilde O(T)$.
--
--   **Formalization Note** The source names a Turing machine with random-access heads and does not spell out how an address is given. The index-tape form is the standard one, and three index tapes suffice for the source's three random-access tapes. The clean tape is unbounded in the semantics; the $s$-bit limit of the source appears as the bound $S$ on the charged space.
-- source:
--   Adelmo Morrison Orozco, Nathan S. Sheffield, Ryan Williams, STOC 2027 submission #494 (October 2026), §2 "Catalytic algorithms", printed p.7 (PDF p.8), and Definition 2.2, printed p.8 (PDF p.9)

import Mathlib

namespace CatalyticSorting494.Sorting

/-- The direction a sequential tape head moves in one step. -/
inductive Move where
  | left
  | stay
  | right

/-- A one-sided binary index tape with a sequential head. The list `cells` is the part of the tape
reached so far; every other cell holds `false`. -/
structure IndexTape where
  cells : List Bool
  head : ℕ

namespace IndexTape

/-- A fresh index tape: one visited cell holding `false`, with the head on it. -/
def initial : IndexTape := ⟨[false], 0⟩

/-- The bit under the head. -/
def read (t : IndexTape) : Bool := t.cells.getD t.head false

/-- The address written on the tape, in binary with the least significant bit in cell `0`. -/
def address (t : IndexTape) : ℕ :=
  t.cells.foldr (fun b acc => b.toNat + 2 * acc) 0

/-- Write `b` under the head, then move. Moving left at cell `0` stays at cell `0`, and moving right
onto a new cell makes that cell (holding `false`) part of the visited region. -/
def update (t : IndexTape) (b : Bool) (m : Move) : IndexTape :=
  let cells' := t.cells.set t.head b
  match m with
  | .left => ⟨cells', t.head - 1⟩
  | .stay => ⟨cells', t.head⟩
  | .right => ⟨if t.head + 1 = cells'.length then cells' ++ [false] else cells', t.head + 1⟩

end IndexTape

/-- The six bits a machine sees in one step: the bit under the head of each of the three index
tapes, and the bit in the input, clean and dirty cell each index tape addresses. -/
structure View where
  inputIndexBit : Bool
  cleanIndexBit : Bool
  dirtyIndexBit : Bool
  inputBit : Bool
  cleanBit : Bool
  dirtyBit : Bool

/-- What a machine does in one step: on each index tape write a bit and move the head; write a bit
into the addressed clean cell and into the addressed dirty cell. There is no write to the input. -/
structure Action where
  inputIndex : Bool × Move
  cleanIndex : Bool × Move
  dirtyIndex : Bool × Move
  cleanWrite : Bool
  dirtyWrite : Bool

/-- A deterministic random-access Turing machine in the sense of Definition 2.2: a finite control
with `numStates` states and a transition table on the six visible bits. The result `none` means
halt. The program is one finite object; it has no parameter depending on the instance. -/
structure Machine where
  numStates : ℕ
  start : Fin numStates
  δ : Fin numStates → View → Option (Fin numStates × Action)

namespace Machine

/-- A configuration. `clean` is the clean work tape and `dirty` the catalytic tape, whose length
never changes. `cleanPeak` is one more than the largest clean address accessed so far. -/
structure Config (M : Machine) where
  state : Fin M.numStates
  inputIndex : IndexTape
  cleanIndex : IndexTape
  dirtyIndex : IndexTape
  clean : ℕ → Bool
  dirty : List Bool
  cleanPeak : ℕ

/-- The initial configuration on catalytic contents `z`: start state, all index tapes fresh (so all
addresses are `0`), and clean tape all zero. -/
def init (M : Machine) (z : List Bool) : M.Config where
  state := M.start
  inputIndex := IndexTape.initial
  cleanIndex := IndexTape.initial
  dirtyIndex := IndexTape.initial
  clean := fun _ => false
  dirty := z
  cleanPeak := 1

/-- The bits visible in configuration `cfg` on input `x`. Reading the input or the catalytic tape
at an address past its end yields `false`. -/
def view (M : Machine) (x : List Bool) (cfg : M.Config) : View where
  inputIndexBit := cfg.inputIndex.read
  cleanIndexBit := cfg.cleanIndex.read
  dirtyIndexBit := cfg.dirtyIndex.read
  inputBit := x.getD cfg.inputIndex.address false
  cleanBit := cfg.clean cfg.cleanIndex.address
  dirtyBit := cfg.dirty.getD cfg.dirtyIndex.address false

/-- One step, of unit cost; `none` means the machine has halted. The catalytic tape has fixed length:
a write at an address past its end changes nothing. -/
def step (M : Machine) (x : List Bool) (cfg : M.Config) : Option M.Config :=
  match M.δ cfg.state (M.view x cfg) with
  | none => none
  | some (q, a) =>
    let cleanIndex' := cfg.cleanIndex.update a.cleanIndex.1 a.cleanIndex.2
    some
      { state := q
        inputIndex := cfg.inputIndex.update a.inputIndex.1 a.inputIndex.2
        cleanIndex := cleanIndex'
        dirtyIndex := cfg.dirtyIndex.update a.dirtyIndex.1 a.dirtyIndex.2
        clean := Function.update cfg.clean cfg.cleanIndex.address a.cleanWrite
        dirty := cfg.dirty.set cfg.dirtyIndex.address a.dirtyWrite
        cleanPeak := max cfg.cleanPeak (cleanIndex'.address + 1) }

/-- The configuration after `t` steps, if the machine has not halted before then. -/
def configAt (M : Machine) (x z : List Bool) : ℕ → Option M.Config
  | 0 => some (M.init z)
  | t + 1 => (M.configAt x z t).bind (M.step x)

/-- The clean bits charged to a configuration: the clean cells accessed so far, plus every visited
cell of the three index tapes. Addresses of all three tapes are thereby charged as clean space.
Visited regions only grow and `cleanPeak` only grows, so at a final configuration this is the
space of the whole run. -/
def cleanSpace {M : Machine} (cfg : M.Config) : ℕ :=
  cfg.cleanPeak + cfg.inputIndex.cells.length + cfg.cleanIndex.cells.length +
    cfg.dirtyIndex.cells.length

end Machine

/-- The final content of the catalytic tape required by Definition 2.2 when the initial content is
`z` and the output is `out`: `out` is XORed into the first `out.length` bits and all others are
unchanged. The clause for `z` shorter than `out` is excluded by `ComputesWithin`. -/
def xorPrefix : List Bool → List Bool → List Bool
  | [], z => z
  | _ :: _, [] => []
  | o :: os, t :: z => xor t o :: xorPrefix os z

/-- The dirty-XOR-output model with resource bounds (Definition 2.2): started on input `x` with
catalytic content `z`, machine `M` halts after at most `T` steps, charged at most `S` clean bits
over the run, with output `out` XORed into the initial segment of the catalytic tape and every other
catalytic bit restored. -/
def ComputesWithin (M : Machine) (x z out : List Bool) (T : ℝ) (S : ℕ) : Prop :=
  out.length ≤ z.length ∧
    ∃ (t : ℕ) (cfg : M.Config),
      M.configAt x z t = some cfg ∧ M.step x cfg = none ∧ (t : ℝ) ≤ T ∧
        Machine.cleanSpace cfg ≤ S ∧ cfg.dirty = xorPrefix out z

/-- The `width` low-order bits of `v`, least significant first: the fixed-width binary fields of
the input encodings. -/
def natBits (width v : ℕ) : List Bool :=
  (List.range width).map v.testBit

/-- The bound `A · T · (log₂(T + 2))^k` expressing `Õ(T)`, where `Õ(T)` abbreviates
`T · poly(log T)`. The shift keeps the logarithm positive at `T = 1`. -/
def softBound (A k T : ℕ) : ℕ :=
  A * T * Nat.log 2 (T + 2) ^ k

end CatalyticSorting494.Sorting



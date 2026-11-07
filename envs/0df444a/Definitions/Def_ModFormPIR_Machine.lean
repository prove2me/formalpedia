-- Prove2me | Definitions.Def_ModFormPIR_Machine
-- name    : ModFormPIR_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:52.215023+00:00
-- url     : https://prove2.me/theorems/9710545e-18fb-4f7c-98d1-a87bdaecf3e8
-- title:
--   The word RAM with a read-only bit table and a coin tape
-- statement:
--   A **program** is a finite list of instructions. An instruction is a word RAM core instruction (write one; add, subtract, multiply modulo $2^W$; indirect load and store at signed addresses; branch on a negative word; accept; reject), or $\mathtt{probe}\ i\ j$, which sets $[i]$ to the bit of a read-only table at address $[j]$ and appends that bit to the run's **trace**, or $\mathtt{coin}\ i$, which sets $[i]$ to the next bit of a coin tape. Every instruction costs one step, and a probe out of range returns $0$ and is still counted. A run starts at position $0$ with the input words in cells $0,1,2,\dots$ and zero in all other cells, negative cells included.
--
--   The file also defines the fair coin measure on tapes, the accept time of a program on a tape ($\infty$ when no accepting run exists), and how outputs are read: bits one per cell, from a base cell downwards.
--
--   The paper counts "word operations" and "reads" of a data structure without naming a machine; this model makes both precise, and it is the setting in which server time and bits read are measured.
--
--   **Formalization Note** The core instructions are the published `TrulySubcubicAPSP.Instr`, with the semantics of its `exec`. Because the bit table is outside the memory, every read of it appears in the trace.
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), §4.1, p.19 (server time) and Definition 5.1, p.21 (bits read); the paper names no machine, so this is a reading

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace ModFormPIR

/-!
# The word RAM with a read-only bit table and a coin tape

Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027
submission (manuscript sha256 2442f3db…), §4.1, p.19 ("number of word operations (including but not
limited to RAM accesses performed)"), and Definition 5.1, p.21 ("reads and sends back at most
`n^{ρ+o(1)}` bits of its data structure").

**Formalization Note.** The paper names no machine; this file is the reading of "word operations".
The arithmetic core is the published `TrulySubcubicAPSP.Instr` (one, add, sub, mul, load, store, branch on
negative, accept, reject). Two instructions are added: `probe i j` reads one bit of a read-only table
stored outside the memory, and appends that bit to the run's trace; `coin i` reads the next bit of a
coin tape. Every instruction costs one step. The trace is what a server sends back, so "reads" and
"sends back" are one list and a server cannot send a bit it did not read.
-/

/-- An instruction: a word RAM core instruction, `probe i j` (`[i] := table[[j]]`, the bit read being
appended to the trace; `0` out of range, and still counted), or `coin i` (`[i] :=` next tape bit). -/
inductive Instr where
  | core (i : TrulySubcubicAPSP.Instr)
  | probe (i j : ℤ)
  | coin (i : ℤ)

/-- A program is a finite list of instructions, independent of the input size and the word width. -/
abbrev Program := List Instr

/-- A machine state: position in the program, memory of `W`-bit words, tape cursor, bits probed so far. -/
structure State (W : ℕ) where
  pc : ℕ
  mem : ℤ → BitVec W
  cursor : ℕ
  trace : List Bool

/-- The memory `m` with cell `i` overwritten by `v`. -/
def setCell {W : ℕ} (m : ℤ → BitVec W) (i : ℤ) (v : BitVec W) : ℤ → BitVec W :=
  fun x => if x = i then v else m x

/-- A bit as a word: `1` or `0`. -/
def bitWord (W : ℕ) (b : Bool) : BitVec W := if b then 1 else 0

/-- The bit of `table` at the signed address `a`; `false` when `a` is out of range. -/
def tableBit (table : List Bool) (a : ℤ) : Bool :=
  if 0 ≤ a then table.getD a.toNat false else false

/-- The verdict and the final state, if `P` with table `table` and coin tape `tape` halts within `t`
steps from `st`, the halting step counted. The core semantics is that of `TrulySubcubicAPSP.exec`:
past its end the program rejects, addresses are read signed, and `bltz` jumps on a negative word. -/
def exec {W : ℕ} (P : Program) (table : List Bool) (tape : ℕ → Bool) :
    (t : ℕ) → State W → Option (Bool × State W)
  | 0, _ => none
  | t + 1, st =>
    let m := st.mem
    let next (m' : ℤ → BitVec W) := exec P table tape t { st with pc := st.pc + 1, mem := m' }
    match P.getD st.pc (.core .reject) with
    | .core (.one i) => next (setCell m i 1)
    | .core (.add i j k) => next (setCell m i (m j + m k))
    | .core (.sub i j k) => next (setCell m i (m j - m k))
    | .core (.mul i j k) => next (setCell m i (m j * m k))
    | .core (.load i j) => next (setCell m i (m (m j).toInt))
    | .core (.store i j) => next (setCell m (m i).toInt (m j))
    | .core (.bltz i l) =>
        exec P table tape t { st with pc := if (m i).toInt < 0 then l else st.pc + 1 }
    | .core .accept => some (true, st)
    | .core .reject => some (false, st)
    | .probe i j =>
        let bit := tableBit table (m j).toInt
        exec P table tape t
          { st with pc := st.pc + 1, mem := setCell m i (bitWord W bit), trace := st.trace ++ [bit] }
    | .coin i =>
        exec P table tape t
          { st with pc := st.pc + 1, mem := setCell m i (bitWord W (tape st.cursor)),
                    cursor := st.cursor + 1 }

/-- The state at the start: position 0, `ws` in cells 0, 1, 2, …, 0 in every other cell (negative cells
included), cursor 0, empty trace. -/
def start (W : ℕ) (ws : List ℤ) : State W :=
  ⟨0, TrulySubcubicAPSP.loadWords W ws, 0, []⟩

/-- `P`, on input words `ws`, with table `table` and coin tape `tape`, accepts within `t` steps, ending
in state `st`. -/
def Accepts {W : ℕ} (P : Program) (table : List Bool) (tape : ℕ → Bool) (ws : List ℤ) (t : ℕ)
    (st : State W) : Prop :=
  exec P table tape t (start W ws) = some (true, st)

/-- A program with no `probe` instruction. -/
def NoProbe (P : Program) : Prop := ∀ i j, Instr.probe i j ∉ P

/-- A program with no `coin` instruction. -/
def NoCoin (P : Program) : Prop := ∀ i, Instr.coin i ∉ P

/-- The fair coin tape: independent fair bits. -/
noncomputable def coinMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ => (PMF.uniformOfFintype Bool).toMeasure

/-- The all-zero tape, passed to programs that have no `coin` instruction. -/
def zeroTape : ℕ → Bool := fun _ => false

/-- The accept time of `P` with table `[]` on tape `τ`: the least `t` of an accepting run, and `⊤` when
no accepting run exists (a rejecting or diverging tape costs `⊤`). -/
noncomputable def acceptCost (P : Program) (W : ℕ) (ws : List ℤ) (τ : ℕ → Bool) : ℝ≥0∞ :=
  ⨅ (t : ℕ) (_ : ∃ st : State W, Accepts P [] τ ws t st), (t : ℝ≥0∞)

/-- A word as a list of `len` cell values: bit `i` (least significant first) of `x`, one per cell. -/
def bitCells (len x : ℕ) : List ℤ :=
  (List.range len).map fun i : ℕ => if x.testBit i then (1 : ℤ) else 0

/-- The bits in cells `base`, `base - 1`, …, `base - (len - 1)`, each read as "the word is 1". -/
def readBits {W : ℕ} (st : State W) (base : ℤ) (len : ℕ) : List Bool :=
  (List.range len).map fun i : ℕ => decide (st.mem (base - (i : ℤ)) = 1)

/-- Every one of the cells `base`, …, `base - (len - 1)` holds the word `0` or the word `1`. -/
def BitCellsOK {W : ℕ} (st : State W) (base : ℤ) (len : ℕ) : Prop :=
  ∀ i : ℕ, i < len → st.mem (base - (i : ℤ)) = 0 ∨ st.mem (base - (i : ℤ)) = 1

/-- The natural number with bits `readBits st base len`, least significant first. -/
def readNat {W : ℕ} (st : State W) (base : ℤ) (len : ℕ) : ℕ :=
  ((readBits st base len).zipIdx.map fun p => if p.1 then 2 ^ p.2 else 0).sum

end ModFormPIR



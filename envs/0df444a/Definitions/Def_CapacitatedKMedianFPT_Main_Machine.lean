-- Prove2me | Definitions.Def_CapacitatedKMedianFPT_Main_Machine
-- name    : CapacitatedKMedianFPT_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:23.711412+00:00
-- url     : https://prove2.me/theorems/221a7407-acc3-46e1-9862-ef8b1f4b901e
-- title:
--   Deterministic rational-cell RAM with a value oracle and unit, word and bit cost
-- statement:
--   The machine model of the algorithmic statements (Theorems 1, 3, 4 and Lemma 1).
--
--   A **program** is a finite list of instructions acting on a memory with one rational number per integer address: load a constant; $+,-,\times,/$ (division by zero gives $0$); floor; indirect load and store (the address is the floor of a cell); a conditional jump on a negative cell; halt; and an **oracle query**, which reads a block of $\ell$ consecutive cells and writes the oracle's answer. A program runs from position $0$ with the input in cells $0,1,2,\dots$ and zero elsewhere; it is deterministic. Each executed step records
--
--   1. a unit charge ($1$, or $1+\ell$ for a query reading $\ell$ cells), and
--   2. its bit size: the total bit length of every address and value read or written.
--
--   From these, three running times are defined:
--
--   $$\mathrm{unit}=\sum_{\text{steps}}\text{unit charge},\qquad \mathrm{word}_w=\sum_{\text{steps}}\max\Bigl(1,\Bigl\lceil\frac{\text{bit size}}{w}\Bigr\rceil\Bigr),\qquad \mathrm{log}=\mathrm{word}_1 .$$
--
--   The bit length of a rational $p/q$ in lowest terms is the number of bits of $|p|$ plus that of $q$. The **input length** $|I|$ of an input list is its number of entries plus the bit lengths of its entries, and the **word length of an input** is the maximal bit length of an entry plus the bit length of the number of entries, plus one. The number of oracle calls is counted separately.
--
--   Logarithmic cost is polynomially equivalent to Turing machines, so $f(k,\varepsilon)\cdot|I|^{O(1)}$ bounds do not depend on the choice. Unit cost is the convention of the value-oracle model; word cost with the input's word length is the transdichotomous word RAM.
--
--   **Formalization Note** `exec` runs with fuel; `RunsTo` asserts halting with the given final memory and statistics. Running past the end of the program halts.
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 1–2, Theorem 1 (running time f(k,ε)·|I|^O(1), |I| the input length); p. 6, Lemma 1 and Theorem 3 (running times); p. 13, Theorem 4 (value oracle model, number of oracle calls and running time); p. 19, Running time

import Mathlib

set_option autoImplicit false

/-!
# A deterministic RAM over rational cells with a value oracle and three cost accounts

The machine model for the algorithmic statements (Theorems 1, 3, 4 and Lemma 1) of
Anand–Huang–Jaiswal–Kumar–Lee–Yadav, STOC 2027 submission #1646.
-/

namespace CapacitatedKMedianFPT.Main

/-- Instructions. `i j l` are fixed cell addresses, `[i]` is the content of cell `i`. -/
inductive Instr where
  | const (i : ℤ) (q : ℚ)          -- [i] := q
  | add (i j l : ℤ)                -- [i] := [j] + [l]
  | sub (i j l : ℤ)                -- [i] := [j] - [l]
  | mul (i j l : ℤ)                -- [i] := [j] * [l]
  | div (i j l : ℤ)                -- [i] := [j] / [l]   (q / 0 = 0)
  | floor (i j : ℤ)                -- [i] := ⌊[j]⌋
  | load (i j : ℤ)                 -- [i] := [⌊[j]⌋]
  | store (i j : ℤ)                -- [⌊[i]⌋] := [j]
  | jneg (i : ℤ) (target : ℕ)      -- if [i] < 0 then jump to position `target`
  | query (i j l : ℤ)              -- [i] := oracle([⌊[j]⌋], [⌊[j]⌋+1], …), ⌊[l]⌋ cells
  | halt
  deriving Inhabited

/-- A program is a finite instruction list; running past its end halts. -/
abbrev Program := List Instr

/-- The memory: one rational per integer address. -/
abbrev Memory := ℤ → ℚ

/-- A value oracle, answering a list of rationals with a rational. -/
abbrev Oracle := List ℚ → ℚ

/-- The oracle that answers `0`: used by algorithms without oracle access. -/
def zeroOracle : Oracle := fun _ => 0

/-- Bit length of a rational: bits of the numerator's absolute value plus bits of the denominator. -/
def bitSizeQ (q : ℚ) : ℕ := Nat.size q.num.natAbs + Nat.size q.den

/-- Bit length of an integer address. -/
def bitSizeZ (z : ℤ) : ℕ := Nat.size z.natAbs

/-- Statistics of a run: number of oracle calls and, per executed step (newest first), the pair
(unit charge, bit size of every address and value read or written in the step). -/
structure Stats where
  queries : ℕ
  trace : List (ℕ × ℕ)

/-- Write `q` into cell `i`. -/
def Memory.set (m : Memory) (i : ℤ) (q : ℚ) : Memory := fun x => if x = i then q else m x

/-- Execute with fuel: `exec P O fuel pc m s` is `some (final memory, stats)` if the program halts
within `fuel` steps (the halting step counted), and `none` otherwise. -/
def exec (P : Program) (O : Oracle) : ℕ → ℕ → Memory → Stats → Option (Memory × Stats)
  | 0, _, _, _ => none
  | fuel + 1, pc, m, s =>
    let tick (u sz : ℕ) (q : ℕ) : Stats := ⟨s.queries + q, (u, sz) :: s.trace⟩
    let arith (i j l : ℤ) (r : ℚ) :=
      exec P O fuel (pc + 1) (m.set i r)
        (tick 1 (bitSizeZ i + bitSizeZ j + bitSizeZ l + bitSizeQ (m j) + bitSizeQ (m l) +
          bitSizeQ r) 0)
    match P.getD pc Instr.halt with
    | .halt => some (m, tick 1 0 0)
    | .const i q => exec P O fuel (pc + 1) (m.set i q) (tick 1 (bitSizeZ i + bitSizeQ q) 0)
    | .add i j l => arith i j l (m j + m l)
    | .sub i j l => arith i j l (m j - m l)
    | .mul i j l => arith i j l (m j * m l)
    | .div i j l => arith i j l (m j / m l)
    | .floor i j =>
      let r : ℚ := (⌊m j⌋ : ℚ)
      exec P O fuel (pc + 1) (m.set i r)
        (tick 1 (bitSizeZ i + bitSizeZ j + bitSizeQ (m j) + bitSizeQ r) 0)
    | .load i j =>
      let a := ⌊m j⌋
      exec P O fuel (pc + 1) (m.set i (m a))
        (tick 1 (bitSizeZ i + bitSizeZ j + bitSizeQ (m j) + bitSizeZ a + bitSizeQ (m a)) 0)
    | .store i j =>
      let a := ⌊m i⌋
      exec P O fuel (pc + 1) (m.set a (m j))
        (tick 1 (bitSizeZ i + bitSizeZ j + bitSizeQ (m i) + bitSizeZ a + bitSizeQ (m j)) 0)
    | .jneg i t =>
      exec P O fuel (if m i < 0 then t else pc + 1) m
        (tick 1 (bitSizeZ i + bitSizeQ (m i) + Nat.size t) 0)
    | .query i j l =>
      let base := ⌊m j⌋
      let len := (⌊m l⌋).toNat
      let args := (List.range len).map (fun t => m (base + t))
      let r := O args
      exec P O fuel (pc + 1) (m.set i r)
        (tick (len + 1) (bitSizeZ i + bitSizeZ j + bitSizeZ l + bitSizeQ (m j) + bitSizeQ (m l) +
          (args.map bitSizeQ).sum + bitSizeQ r) 1)

/-- The initial memory: the input in cells `0, 1, 2, …`, zero elsewhere. -/
def initMemory (input : List ℚ) : Memory :=
  fun a => if 0 ≤ a then input.getD a.toNat 0 else 0

/-- Starting at position 0 on `input`, the program halts with final memory `m` and statistics
`s`. Execution is deterministic; the existential is only over the fuel. -/
def RunsTo (P : Program) (O : Oracle) (input : List ℚ) (m : Memory) (s : Stats) : Prop :=
  ∃ fuel, exec P O fuel 0 (initMemory input) ⟨0, []⟩ = some (m, s)

namespace Stats

/-- Unit-cost time: one per step, `1 + len` for an oracle call reading `len` cells. -/
def unitTime (s : Stats) : ℕ := (s.trace.map Prod.fst).sum

/-- Word-RAM time with word length `w`: a step whose operands have `b` bits in total costs
`max 1 ⌈b / w⌉` (operations on multi-word values cost per word). -/
def wordTime (s : Stats) (w : ℕ) : ℕ :=
  (s.trace.map (fun p => max 1 ((p.2 + max 1 w - 1) / max 1 w))).sum

/-- Logarithmic-cost (bit) time: `wordTime` with one-bit words. -/
def logTime (s : Stats) : ℕ := s.wordTime 1

end Stats

/-- The input length `|I|` in bits: one per entry plus the bit lengths of all entries. -/
def inputLength (input : List ℚ) : ℕ := input.length + (input.map bitSizeQ).sum

/-- The transdichotomous word length of an input: enough bits for every input entry and for the
input's length. -/
def wordSizeOf (input : List ℚ) : ℕ :=
  (input.map bitSizeQ).foldr max 0 + Nat.size input.length + 1

end CapacitatedKMedianFPT.Main



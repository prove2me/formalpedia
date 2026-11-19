-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_NativeWordRAM
-- name    : EdgeSublinearMWIS_Main_NativeWordRAM
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T08:34:10.908612+00:00
-- url     : https://prove2.me/theorems/c2c08711-e29e-4054-ac4f-0a96ce1b1807
-- title:
--   Finite word-RAM execution and canonical binary word encoding
-- statement:
--   This module fixes a deterministic finite word-RAM model and its input representation. A program is a finite instruction list. Configurations carry the accumulator, zero-initialized random-access memory, input position and output words. The transition semantics specifies arithmetic at a supplied word width and counts the executed instructions through halting.
--
--   A list of natural words is encoded by a separator followed by each word's least-significant-bit-first binary expansion. Its size is
--   $$
--   \operatorname{bits}(x)=\sum_{a\in x}\bigl(1+\operatorname{bitlength}(a)\bigr).
--   $$
--   The physical RAM input includes the list length as its first word. The module also defines the word-fit condition and uniform polynomial-time predicate. For the mission's Boolean machine interface, separator, zero and one are encoded respectively as $00$, $01$ and $10$.
--
--   These are data types and operational definitions. No program correctness, simulation theorem or complexity bound is assumed.
-- source:
--   Word-RAM model: https://github.com/lax-archive/lax-submissions/tree/9394e531cc51cb67a0214bca3f9264dfe97ba5c7/word-ram/concepts/Lax808846, Ram.lean. Canonical encoding and polynomial-time predicate: https://github.com/szymtor/RAM-TM/tree/134e398cef46599371df99f10c9007bc34ba3868/concepts/Lax759944, BinaryWordEncoding.lean and RamPolytime.lean. Boolean pair coding is the explicit TernaryAdapter.symbolBits/binarySymbols and RamBridge.wordBits adapter used in this mission.

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding

-- Solutions.RAM_Lax808846_Ram
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: The word RAM
type: definition
---
A word RAM is a random access machine whose writable memory consists of
`2 ^ w` cells holding natural numbers below `2 ^ w`. The word length
`w` is a parameter; one finite program serves all word lengths. Input
is a read-only finite array supplied at initialization, also accessible
as a sequential tape. Output is an append-only tape. Working memory
starts at zero and output starts empty.

The input interface has four operations. `read a` consumes the next
entry of the sequential tape into cell `a`, halting if the tape is
empty. `jeof l` branches on tape emptiness without consuming input.
`inputLength a` writes the original input length into cell `a`.
`inputLoad a b` reads the original input at the index in cell `b` into
cell `a`, returning zero outside the input. Indexed access never
consumes the sequential tape, and sequential reads never change the
original input. Zero is ordinary data, not an end marker. Each operation
costs one instruction. No length header or other framing is added to
the supplied list.

Arithmetic results, input values and lengths, output values, and
data-memory addresses are reduced modulo `2 ^ w`. Subtraction is
truncated at zero, and division is integer division with `x / 0 = 0`.
Input indices are words too. Program labels and the program counter are
natural numbers and are not reduced modulo `2 ^ w`.

# Formalization notes

The register-transfer format follows Cook and Reckhow (*Time bounded
random access machines*, JCSS 7, 1973): instructions act on numbered
cells, with indirection through a cell holding an address. Their cells
hold signed integers, and their sequential input has a distinguished
zero end marker outside its input alphabet. This definition instead
uses unsigned words, supplies explicit EOF detection, and additionally
provides indexed read-only input with its length available in constant
time. It therefore specifies its own input convention; the interface
is not an identification with the original Cook--Reckhow input tape.

Word operations have unit cost, as in the bounded-word models of
Fredman and Willard (*Surpassing the information theoretic bound with
fusion trees*, JCSS 47, 1993) and Hagerup (*Sorting and searching on the
word RAM*, STACS 1998). Comparisons with other word-RAM presentations
must fix the available operations, input convention, and address-space
assumptions. Indexed input avoids a compulsory input scan, as in an
input-array RAM. A simulation that instead starts from sequential input
and loads an `n`-word array pays an additive `O(n)` cost, giving
`O(n + T)`, which is `O(T)` only under a suitable lower bound on `T`.
No unconditional constant-factor model-equivalence claim is made here.

`setCell` reduces each value stored and each destination address modulo
`2 ^ w`. Other data-memory operands and indirect addresses are reduced
at use; output and input values are reduced too. From initialization,
every reachable memory cell holds a word. The function representation
of memory has domain `ℕ`, but execution accesses only the residues below
`2 ^ w`. Program control is separate: `jump`, `jzero`, and `jeof` use
untruncated program labels, ordinary advancement increments the full
program counter, and instruction fetch uses that counter.

Oversized input entries and the length are reduced rather than
rejected. To recover an entry unchanged requires that entry to be below
`2 ^ w`; to recover the complete original length with `inputLength`
requires `x.length < 2 ^ w`. These fitting conditions belong in the
admissible domain of the theorem that needs them. EOF-based programs
can process lists whose total length does not fit in a word. Indexed
reads can address the prefix with indices below `2 ^ w`; the initial
array itself is read-only input storage, separate from writable memory.

Subtraction is natural-number monus, so a comparison is `sub` followed
by `jzero`. Complement is `2 ^ w - 1 - m[b]`. No instruction returns
the word length. The following operations are derived at constant cost,
with scratch cells `t` and `u` whose physical addresses modulo `2 ^ w`
are distinct from each other and from every operand's physical address.
Distinct natural-number literals alone do not ensure this condition:

| operation | instructions | count |
|---|---|---|
| copy `a ← b` | `set t b; load a t` | 2 |
| `a ← b ∨ c` | `and t b c; sub t c t; add a b t` | 3 |
| `a ← b ⊕ c` | `and t b c; sub u c t; add u b u; sub a u t` | 4 |
| `a ← b ≫ c` | `set t 1; shiftl t t c; div a b t` | 3 |
| `a ← b mod c` | `div t b c; mul t t c; sub a b t` | 3 |
| if `b ≤ c` goto `l` | `sub t b c; jzero t l` | 2 |
| if `b < c` goto `l` | `sub t c b; jzero t l'; jump l; l':` | 3 |
| if `b = c` goto `l` | `sub t b c; sub u c b; add t t u; jzero t l` | 4 |

An explicit `halt`, an exhausted `read`, or an out-of-range program
counter terminates execution. `step` returns `none` in all three cases.
`run w p k` counts successful transitions only. `RunsTo` adds the cost
of the fetched terminal instruction: one for `halt` or exhausted `read`,
and zero for an out-of-range counter, where no instruction exists.
Thus `RunsTo` counts every executed instruction exactly once, and an
empty program costs zero. Termination constrains the entire output
tape; memory is left unconstrained.

The separate read-only input preserves a fixed working-memory layout.
An input-in-memory convention could also reserve fixed low-address
working cells and put input at a fixed base; no length-dependent input
base is necessary. Copying this model's input into writable memory,
when desired and when the chosen layout fits, takes constant overhead
per word and linear total time: a uniform loader uses `read` into a
temporary cell, an indirect `store`, and loop maintenance.

There is no separate space measure or randomness primitive. A space
measure can be defined over executions; writable memory has `2 ^ w`
cells. A deterministic program can consume additional input words to
model supplied random choices.
-/

namespace Lax808846.Ram

/-- An instruction. Every number naming a cell is read, except that
the first one names the destination for instructions that write a cell,
and the cell holding the destination address for `store`. `set` carries
a literal value; `jump`, `jzero`, and `jeof` carry program labels,
which are not data-memory addresses. -/
inductive Instr
  /-- Set cell `a` to the literal `n`. -/
  | set (a n : ℕ)
  /-- Set cell `a` to the contents of the cell whose address cell `b`
  holds. -/
  | load (a b : ℕ)
  /-- Set the cell whose address cell `a` holds to the contents of cell
  `b`. -/
  | store (a b : ℕ)
  /-- Set cell `a` to the sum of cells `b` and `c`, wrapping around
  modulo `2 ^ w`. -/
  | add (a b c : ℕ)
  /-- Set cell `a` to the difference of cells `b` and `c`, truncated at
  zero rather than wrapping around. -/
  | sub (a b c : ℕ)
  /-- Set cell `a` to the product of cells `b` and `c`, wrapping around
  modulo `2 ^ w`. -/
  | mul (a b c : ℕ)
  /-- Set cell `a` to the quotient of cells `b` and `c`, rounding
  towards zero; division by zero yields zero. -/
  | div (a b c : ℕ)
  /-- Set cell `a` to the bitwise conjunction of cells `b` and `c`. -/
  | and (a b c : ℕ)
  /-- Set cell `a` to cell `b` shifted left by the number of bits cell
  `c` holds, wrapping around modulo `2 ^ w`; a shift by `w` or more
  yields zero. -/
  | shiftl (a b c : ℕ)
  /-- Set cell `a` to the bitwise complement `2 ^ w - 1 - m[b]` of cell
  `b` within the word length. -/
  | not (a b : ℕ)
  /-- Continue at instruction `l`. -/
  | jump (l : ℕ)
  /-- Continue at instruction `l` if cell `a` is zero. -/
  | jzero (a l : ℕ)
  /-- Continue at instruction `l` exactly when the remaining input tape
  is empty. This test does not consume input. -/
  | jeof (l : ℕ)
  /-- Write the original input length, reduced to a word, into cell `a`. -/
  | inputLength (a : ℕ)
  /-- Read original input at the word index in cell `b` into cell `a`,
  returning zero outside the input. Read the index before writing `a`,
  even when the two cell addresses coincide. Do not consume input. -/
  | inputLoad (a b : ℕ)
  /-- Halt. -/
  | halt
  /-- Read the next number of the input tape into cell `a`, or halt if
  the tape is exhausted. -/
  | read (a : ℕ)
  /-- Append the contents of cell `a` to the output tape. -/
  | write (a : ℕ)

/-- A program: a finite sequence of instructions, numbered from `0`. -/
abbrev Program : Type := List Instr

/-- A machine state: the program counter, the contents of every memory
cell, the immutable original input array, the remaining sequential input
tape, and the output tape written so far. -/
structure State where
  /-- The number of the instruction to be executed next. -/
  pc : ℕ
  /-- The contents of the memory cells; only the cells with number below
  `2 ^ w` are ever addressed. -/
  mem : ℕ → ℕ
  /-- The original read-only input, unchanged by every instruction. -/
  input : List ℕ
  /-- The numbers still to be read from the input tape. -/
  inp : List ℕ
  /-- The numbers written to the output tape so far. -/
  out : List ℕ

/-- The memory `m` with cell `a` set to `v`, at word length `w`: the
address and the value written are both taken modulo `2 ^ w`. -/
def setCell (w : ℕ) (m : ℕ → ℕ) (a v : ℕ) : ℕ → ℕ :=
  fun b => if b = a % 2 ^ w then v % 2 ^ w else m b

/-- The effect of one instruction on the state at word length `w`, or
`none` if it halts the machine, which a `halt` instruction and a read
from an exhausted input tape do. Data values, input indices, and
data-memory addresses are reduced modulo `2 ^ w`; program labels and
the counter are not. -/
def Instr.effect (w : ℕ) : Instr → State → Option State
  | set a n, s => some { s with pc := s.pc + 1, mem := setCell w s.mem a n }
  | load a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (s.mem (b % 2 ^ w) % 2 ^ w)) }
  | store a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem (s.mem (a % 2 ^ w)) (s.mem (b % 2 ^ w)) }
  | add a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) + s.mem (c % 2 ^ w)) }
  | sub a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) - s.mem (c % 2 ^ w)) }
  | mul a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) * s.mem (c % 2 ^ w)) }
  | div a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) / s.mem (c % 2 ^ w)) }
  | and a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (Nat.land (s.mem (b % 2 ^ w)) (s.mem (c % 2 ^ w))) }
  | shiftl a b c, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (s.mem (b % 2 ^ w) * 2 ^ s.mem (c % 2 ^ w)) }
  | not a b, s =>
      some
        { s with
          pc := s.pc + 1
          mem := setCell w s.mem a (2 ^ w - 1 - s.mem (b % 2 ^ w)) }
  | jump l, s => some { s with pc := l }
  | jzero a l, s => some { s with pc := if s.mem (a % 2 ^ w) = 0 then l else s.pc + 1 }
  | jeof l, s => some { s with pc := if s.inp.isEmpty then l else s.pc + 1 }
  | inputLength a, s =>
      some { s with pc := s.pc + 1, mem := setCell w s.mem a s.input.length }
  | inputLoad a b, s =>
      some { s with
        pc := s.pc + 1
        mem := setCell w s.mem a (s.input[s.mem (b % 2 ^ w) % 2 ^ w]?.getD 0) }
  | halt, _ => none
  | read a, s =>
      s.inp.head?.map fun v =>
        { s with pc := s.pc + 1, mem := setCell w s.mem a v, inp := s.inp.tail }
  | write a, s =>
      some { s with pc := s.pc + 1, out := s.out ++ [s.mem (a % 2 ^ w) % 2 ^ w] }

/-- One step of the machine at word length `w`: fetch the instruction
the program counter points at and execute it. The result is `none` if
the machine has halted, which also happens when the program counter has
run past the program. -/
def step (w : ℕ) (p : Program) (s : State) : Option State :=
  p[s.pc]?.bind fun i => i.effect w s

/-- The state after `t` successful transitions at word length `w`, or
`none` if one of those transitions terminates. This auxiliary count does
not include a fetched terminal instruction; `RunsTo` charges that too. -/
def run (w : ℕ) (p : Program) : ℕ → State → Option State
  | 0, s => some s
  | t + 1, s => (step w p s).bind (run w p t)

/-- The initial state on input `x`: program counter zero, all memory
cells zero, the original input array and its sequential tape both `x`,
and the output tape empty. -/
def initState (x : List ℕ) : State where
  pc := 0
  mem := fun _ => 0
  input := x
  inp := x
  out := []

/-- Cost of termination at `s`, when `step w p s = none`: a fetched
terminal instruction costs one, while an out-of-range program counter
costs zero because there is no instruction to execute. -/
def terminalCost (p : Program) (s : State) : ℕ :=
  if s.pc < p.length then 1 else 0

/-- Started on input `x` at word length `w`, the machine executes
exactly `t` instructions and then halts, having written the word `y` to
its output tape. -/
def RunsTo (w : ℕ) (p : Program) (x y : List ℕ) (t : ℕ) : Prop :=
  ∃ (k : ℕ) (s : State), run w p k (initState x) = some s ∧
    step w p s = none ∧ s.out = y ∧ t = k + terminalCost p s

end Lax808846.Ram

end

-- Solutions.RAM_Lax759944_BinaryWordEncoding
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Binary encoding of finite words
type: definition
---
A finite list of natural numbers is encoded over a three-symbol alphabet.
Each number begins with a separator and is followed by its canonical
least-significant-bit-first binary expansion. Thus zero is represented by a
separator with no following bits, and the next separator begins the next
number. The empty list is represented by the empty string.

This encoding is self-delimiting at the level of numbers: separators cannot
occur as binary digits. Its length is the common input-size measure used by
the Turing-machine and word-RAM polynomial-time definitions in this
submission.
-/

-- Preserve definition unfolding in the generated Fintype instance.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944.BinaryWordEncoding

/-- The finite alphabet used to encode lists of natural numbers. -/
inductive Symbol
  | separator
  | zero
  | one
  deriving DecidableEq, Fintype, Inhabited

/-- Encode one natural number, including the separator which begins it. -/
def encodeNat (n : ℕ) : List Symbol :=
  .separator :: n.bits.map (fun b => if b then .one else .zero)

/-- The canonical binary encoding of a finite list of natural numbers. -/
def encode (x : List ℕ) : List Symbol :=
  x.flatMap encodeNat

/-- The bit-size of a finite list of natural numbers. -/
def bitSize (x : List ℕ) : ℕ :=
  (encode x).length

end Lax759944.BinaryWordEncoding

end

-- Solutions.RAM_Lax759944_RamPolytime
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Polynomial-time computation by a word RAM
type: definition
---
A total function from finite lists of natural numbers to finite lists of
natural numbers is computable in polynomial time by a word RAM when there
are one uniform program, a polynomial word-length bound, and a polynomial
running-time bound with the following property.

For an input whose canonical binary encoding has length *n*, the RAM receives
the physical tape `x.length :: x`. Every tape and output entry fits in a word
of the bounded length, and at every word length at least that bound the program
returns the exact output within the bounded number of RAM instructions. Both
polynomials are evaluated at *n*.

The length prefix is this submission's explicit encoding, supplied unchanged
to Lax808846's read-only input array and sequential tape. It is not added by
the machine. Working memory starts at zero and output is append-only. Programs
may use EOF testing, input length, and indexed input; an executed terminal
instruction is included in the time bound.

Measuring input size in bits, rather than in the number of entries, puts the
RAM and Turing machine on the same input-size scale. Requiring correctness
at every sufficiently large word length makes the program uniform in the
word length. Requiring a polynomial sufficient word length is what permits
a Turing machine to simulate each operation on a word in polynomial time.
No lower bound such as logarithmic word length is separately necessary:
the explicit fitting condition says directly that the length prefix, all
native input entries, and all exact output entries are representable.
-/

namespace Lax759944.RamPolytime

open Lax808846.Ram
open Lax759944.BinaryWordEncoding

/-- Every entry of `x` is representable by a word of `w` bits. -/
def FitsInWords (w : ℕ) (x : List ℕ) : Prop :=
  ∀ a ∈ x, a < 2 ^ w

/-- Polynomial-time computation by one uniform word-RAM program, measured
in the bit-size of the logical word-list input. The physical input is explicitly
length-prefixed. All instructions of Lax808846 are available, including access
to the immutable original input independently of sequential reads. -/
def RamPolytime (f : List ℕ → List ℕ) : Prop :=
  ∃ (p : Program) (wordBound timeBound : Polynomial ℕ),
    ∀ x : List ℕ,
      FitsInWords (wordBound.eval (bitSize x)) ((x.length :: x) ++ f x) ∧
        ∀ w : ℕ, wordBound.eval (bitSize x) ≤ w →
          ∃ t ≤ timeBound.eval (bitSize x),
            RunsTo w p (x.length :: x) (f x) t

end Lax759944.RamPolytime

end

-- Solutions.TernaryMachineCode
section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace EdgeSublinearMWIS.Main.TernaryAdapter
open Turing.TM2 Lax759944.BinaryWordEncoding

 def firstBit : Symbol → Bool
   | .one => true
   | _ => false
 def secondBit : Symbol → Bool
   | .zero => true
   | _ => false
 
 def symbolBits (s : Symbol) : List Bool := [firstBit s,secondBit s]
 def binarySymbols (xs : List Symbol) : List Bool := xs.flatMap symbolBits
 
 

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
end EdgeSublinearMWIS.Main.TernaryAdapter

end
end

-- Solutions.NativeWordRAMBitProgram
section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace EdgeSublinearMWIS.Main.RamBridge
open Lax759944.BinaryWordEncoding TernaryAdapter

 def wordBits (xs : List ℕ) : List Bool := binarySymbols (encode xs)

 

end EdgeSublinearMWIS.Main.RamBridge

end
end



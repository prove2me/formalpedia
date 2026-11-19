-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_NativeOperationalInterfaces
-- name    : EdgeSublinearMWIS_Main_NativeOperationalInterfaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T11:29:17.671639+00:00
-- url     : https://prove2.me/theorems/2779110d-d369-405d-812c-30537f49ec68
-- title:
--   Operational interfaces for ellipsoid steps and finite RAM simulation
-- statement:
--   These definitions expose the finite tape interpreter clock and the rational ellipsoid state used by the MWIS implementation. They include the rounded shape and center, the intermediate coefficient and update commands, and the stored linear-feasibility predicates. For a word bound $W$ and time bound $T$, the interpreter clock is an explicit polynomial in binary input size and executed RAM steps. All transition rules, workspaces and rational rounding operations remain the definitions of the cited implementations; correctness and clock bounds are separate theorem obligations.
-- source:
--   Bonnet–Chang, Theorem 2 and §5, pp. 2, 12–20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf; operational definitions from lax-109476 commit 0a042604c7ae1ef4cd9a4c7d82eb902f313d4864 (RamEllipsoidStep, RamEllipsoidCoefficients, RamCenterUpdate, RamShapeUpdate, RamCertificateDecision) and RAM-TM commit 134e398cef46599371df99f10c9007bc34ba3868 (RamToTM, TapeRamGenericTime).

import Mathlib.Data.List.Basic
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Cast.Field
import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces
open scoped BigOperators Matrix
open Polynomial Turing

-- Solutions.RAM_Lax759944Proofs_Legacy_Ram
section
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.
-- Adapted 2026-09-15 from word-ram-v4-33 at 0aa87e1f6e6add4abe4f4e0aff8fe4a28950b2ea.
-- Namespace relocated for use as a proof-only intermediate; semantics unchanged.

/-!
A word RAM is a random access machine whose cells hold *words*: natural
numbers below `2 ^ w`, for a word length `w` that is a parameter of the
model. It has a memory of `2 ^ w` cells, addressed by number, and no
other storage. Input arrives on a read-only input tape and output is
written on a write-only output tape. A program is a finite sequence of
instructions, executed in order unless a jump instruction changes the
program counter. Every instruction names the cells it works on: it sets
a cell to a literal; it reads or writes a cell through the address held
in another cell; it sets a cell to the sum, the difference, the product,
the quotient, the bitwise conjunction or the left shift of two cells, or
to the bitwise complement of one; it jumps unconditionally or if a cell
is zero; it halts; or it reads the next input number into a cell or
writes a cell to the output tape.

All arithmetic is arithmetic on words: every value the machine produces
is taken modulo `2 ^ w`, and every address is taken modulo `2 ^ w`.
Subtraction is truncated at zero rather than wrapping. Division is
integer division, with `x / 0 = 0`.

The machine starts with all memory cells zero, the whole input word on
the input tape and the output tape empty; it halts having written the
output word. The running time is the number of instructions executed,
each costing one time unit.

# Formalization notes

This is the machine the modern analysis of algorithms is stated on. Its
format is that of Cook and Reckhow (*Time bounded random access
machines*, JCSS 7, 1973): memory cells are the only storage, an
instruction is `cell ← f(cells)`, literals enter through one instruction
and indirection through two. Its numbers are bounded rather than its
instruction set, which is the discipline of Fredman and Willard
(*Surpassing the information theoretic bound with fusion trees*, JCSS
47, 1993) and of Hagerup (*Sorting and searching on the word RAM*,
STACS 1998): cells hold `w`-bit words, `w` is large enough to address
the input — `w ≥ log n`, here always written as an explicit inequality
against `2 ^ w` at the point of use — and a word operation costs one
time unit because on words it is one instruction of a real machine.
Multiplication, division, bitwise operations and shifts are then
unproblematic, and this is what makes the model the one in which the
results of the algorithms literature are actually stated. The formats
in which those results are written down simulate one another with
constant overhead (van Emde Boas, *Machine models and simulations*,
Handbook of Theoretical Computer Science A, 1990, §2).

Truncation is definitional and follows a single rule, applied
everywhere and with no exceptions: **every value the machine produces
is reduced modulo `2 ^ w` at the point of production, and every address
is reduced modulo `2 ^ w` at the point of use.** Values are produced
into memory, where `setCell` carries the reduction, and onto the output
tape, where `Instr.effect` writes it out; addresses are used by every
operand of every instruction, by the address `load` and `store` fetch
out of a cell, and by `setCell` when it writes. A literal is not
reduced where it is written down — that would be a second rule — but
the value it produces is, so an oversized literal is never observable
except through a word, and only a program's own literals can be
oversized in the first place, since every value it can read out of
memory is a word. Two consequences make the rule worth its uniformity:
every cell the machine can reach holds a word, by construction rather
than by an invariant to be proved; and the memory, although indexed by
all of `ℕ`, is touched only at the residues below `2 ^ w`, so it is
exactly the canonical `2 ^ w`-cell store. For the instructions whose
results cannot leave the words — truncated subtraction, division,
conjunction, complement — the reduction does nothing; it is written
anyway, because a rule without exceptions is easier to review than a
case distinction.

Subtraction is natural-number monus, truncated at zero, so that a
comparison is `sub` followed by `jzero`. The complement is
`2 ^ w - 1 - m[b]`, the one value that depends on the word length other
than through truncation; with `and` and `shiftl` beside it, every
bitwise operation and both shifts take a number of instructions
independent of `w`. A program measures `w` itself, by counting the
doublings of a cell from `1` until it wraps to zero, so the model needs
no instruction reporting the word length and one program serves every
word length. The remaining standard operations are derived at constant
cost; with `t` and `u` cells the program spares:

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

`read` reduces the number it takes off the input tape modulo `2 ^ w`,
like every other value, so the machine is total in its input and
honesty about inputs whose entries do not fit into a word lives on the
statement side, in the set of admissible inputs a claim quantifies
over.

Reading and writing are total: a `halt` instruction halts the machine,
an out-of-range program counter halts it, a read from an exhausted
input tape halts it, and every memory cell holds a number, so no error
states are needed. `Instr.effect` is the whole of the instruction
semantics and `step` adds only the fetch, returning `none` exactly when
the machine has halted, so the semantics is deterministic and total by
construction. `run w p t` is `t`-fold application of `step`, and it is
`none` as soon as the machine halts, which is what makes "halts after
exactly `t` steps" in `RunsTo` a statement about the *number of
instructions executed*: the time measure is intrinsic to the machine
and is not an annotation carried alongside the program. `RunsTo`
constrains the output tape and nothing else: memory is scratch space
and is left unconstrained on halting.

The input and output tapes are what makes the machine's memory start
out empty, and hence what lets a program address it by fixed cell
numbers; an input laid out in memory instead would begin at a cell
number depending on the input length. A program that wants random
access to its input copies it into memory first, at a cost of one
instruction per number.

Time is the machine's own step count, one unit per instruction, and it
is honest for multiplication precisely because the factors are words.
There is no space measure: it would be a further definition over `run`,
and space is in any case bounded by the `2 ^ w` cells the machine can
address. Randomness is absent as well; a randomized program is a
deterministic program that consumes a word list of random numbers,
which is definable downstream over this same machine, with no change to
the model.
-/

namespace Lax759944Proofs.Legacy.Ram

/-- An instruction. The first cell named is the one written, and every
other number naming a cell is read; `set` is the only instruction
carrying a literal, and `jump`, `jzero` carry a program address. -/
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
cell, the part of the input tape not yet read, and the output tape
written so far. Memory is the only storage there is. -/
structure State where
  /-- The number of the instruction to be executed next. -/
  pc : ℕ
  /-- The contents of the memory cells; only the cells with number below
  `2 ^ w` are ever addressed. -/
  mem : ℕ → ℕ
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
from an exhausted input tape do. Every value produced is reduced modulo
`2 ^ w` and every address used is reduced modulo `2 ^ w`. -/
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

/-- The state after `t` steps at word length `w`, or `none` if the
machine halts before executing `t` instructions. -/
def run (w : ℕ) (p : Program) : ℕ → State → Option State
  | 0, s => some s
  | t + 1, s => (step w p s).bind (run w p t)

/-- The initial state on input `x`: program counter zero, all memory
cells zero, the input word on the input tape, the output tape empty. -/
def initState (x : List ℕ) : State where
  pc := 0
  mem := fun _ => 0
  inp := x
  out := []

/-- Started on input `x` at word length `w`, the machine executes
exactly `t` instructions and then halts, having written the word `y` to
its output tape. -/
def RunsTo (w : ℕ) (p : Program) (x y : List ℕ) (t : ℕ) : Prop :=
  ∃ s : State, run w p t (initState x) = some s ∧ step w p s = none ∧ s.out = y

end Lax759944Proofs.Legacy.Ram

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_PolynomialBounds
section
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM





/-- A concrete coefficient sum used to dominate a natural-coefficient
polynomial by one monomial. -/
def polyCoeffSum (p : Polynomial ℕ) : ℕ :=
  p.support.sum p.coeff



/-- Every natural-coefficient polynomial is bounded by the especially
simple polynomial `C coeffSum * (X + 1)^natDegree`.  This normal form is
what the reverse TM interpreter computes as its word budget. -/
noncomputable def polynomialSimpleMajorant (p : Polynomial ℕ) : Polynomial ℕ :=
  C (polyCoeffSum p) * (X + 1) ^ p.natDegree





end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FiniteSimulation
section
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode

noncomputable section



























































































































































































































































noncomputable def coreSimulationPolynomial
    (wordBound timeBound : Polynomial Nat) : Polynomial Nat :=
  Polynomial.C 1000 * timeBound * (timeBound + 1) *
    (wordBound + 2) ^ 2







end

end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_WrapperEmbedding
section
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM


open Lax759944.BinaryWordEncoding

noncomputable section

inductive WrapperStack
  | input
  | output
  | core (stack : CoreStack)
  deriving DecidableEq, Fintype, Inhabited

def WrapperAlphabet : WrapperStack -> Type
  | .input | .output => Symbol
  | .core _ => SparseSymbol







structure WrapperState (N : Nat) where
  core : FullInterpreterState N := default
  heldInput : Option Symbol := none
  heldSparse : Option SparseSymbol := none
  flag : Bool := false
  active : Bool := false
  deriving DecidableEq, Fintype, Inhabited

def WrapperState.coreLens {N : Nat} :
    StateLens (FullInterpreterState N) (WrapperState N) where
  get := WrapperState.core
  put := fun s core => {s with core}
  get_put := by intros; rfl
  put_get := by intro s; cases s; rfl
  put_put := by intros; rfl





def liftCoreStmt {N : Nat} {L X : Type}
    (stmt : TM2.Stmt (fun _ : CoreStack => SparseSymbol) L
      (FullInterpreterState N)) :
    TM2.Stmt WrapperAlphabet (Sum L X) (WrapperState N) :=
  match stmt with
  | .push k f q => .push (.core k) (fun s => f s.core) (liftCoreStmt q)
  | .peek k f q => .peek (.core k)
      (fun s a => WrapperState.coreLens.put s (f s.core a)) (liftCoreStmt q)
  | .pop k f q => .pop (.core k)
      (fun s a => WrapperState.coreLens.put s (f s.core a)) (liftCoreStmt q)
  | .load f q => .load
      (fun s => WrapperState.coreLens.put s (f s.core)) (liftCoreStmt q)
  | .branch f q₁ q₂ => .branch (fun s => f s.core)
      (liftCoreStmt q₁) (liftCoreStmt q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.core))
  | .halt => .halt











end

end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_OutputAdapter
section
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

-- Preserve Lean 4.30 elaboration for derived finite instances.
set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM


open Lax759944.BinaryWordEncoding

noncomputable section









inductive CleanupStack
  | input
  | core (stack : CoreStack)
  deriving DecidableEq, Fintype, Inhabited

def cleanupStack : CleanupStack -> WrapperStack
  | .input => .input
  | .core stack => .core stack

def nextCleanupStack : CleanupStack -> Option CleanupStack
  | .input => some (.core .accumulator)
  | .core .accumulator => some (.core .memory)
  | .core .memory => some (.core .input)
  | .core .input => some (.core .output)
  | .core .output => some (.core .work0)
  | .core .work0 => some (.core .work1)
  | .core .work1 => some (.core .work2)
  | .core .work2 => some (.core .work3)
  | .core .work3 => some (.core .work4)
  | .core .work4 => some (.core .work5)
  | .core .work5 => some (.core .work6)
  | .core .work6 => some (.core .work7)
  | .core .work7 => none

inductive OutputAdapterLabel
  | initializeState
  | scan
  | decide
  | bit
  | delimiter
  | finish
  | cleanupPeek (stack : CleanupStack)
  | cleanupPop (stack : CleanupStack)
  | halt
  deriving DecidableEq, Fintype, Inhabited

def outputAdapterProgram {N : Nat} {L : Type} : OutputAdapterLabel ->
    TM2.Stmt WrapperAlphabet (Sum L OutputAdapterLabel) (WrapperState N)
  | .initializeState =>
      .load (fun s => {s with heldSparse := none, flag := false, active := false}) <|
      .goto fun _ => .inr .scan
  | .scan =>
      .pop (.core .output) (fun s a => {s with heldSparse := a}) <|
      .goto fun _ => .inr .decide
  | .decide =>
      .branch (fun s => s.heldSparse = some .outputEnd)
        (.goto fun _ => .inr .finish) <|
      .branch (fun s => s.heldSparse = some .wordEnd)
        (.goto fun _ => .inr .delimiter) <|
      .goto fun _ => .inr .bit
  | .bit =>
      .branch (fun s => s.heldSparse = some (.bit true))
        (.push .output (fun _ => .one) <|
          .load (fun s => {s with heldSparse := none, flag := true}) <|
          .goto fun _ => .inr .scan) <|
      .branch (fun s => s.flag)
        (.push .output (fun _ => .zero) <|
          .load (fun s => {s with heldSparse := none}) <|
          .goto fun _ => .inr .scan)
        (.load (fun s => {s with heldSparse := none}) <|
          .goto fun _ => .inr .scan)
  | .delimiter =>
      .branch (fun s => s.active)
        (.push .output (fun _ => .separator) <|
          .load (fun s => {s with heldSparse := none, flag := false, active := true}) <|
          .goto fun _ => .inr .scan)
        (.load (fun s => {s with heldSparse := none, flag := false, active := true}) <|
          .goto fun _ => .inr .scan)
  | .finish =>
      .branch (fun s => s.active)
        (.push .output (fun _ => .separator) <|
          .goto fun _ => .inr (.cleanupPeek .input))
        (.goto fun _ => .inr (.cleanupPeek .input))
  | .cleanupPeek stack =>
      .peek (cleanupStack stack)
        (fun s a => {s with flag := a.isSome}) <|
      .branch (fun s => s.flag)
        (.goto fun _ => .inr (.cleanupPop stack)) <|
      match nextCleanupStack stack with
      | some next => .goto fun _ => .inr (.cleanupPeek next)
      | none => .goto fun _ => .inr .halt
  | .cleanupPop stack =>
      .pop (cleanupStack stack) (fun s _ => s) <|
      .goto fun _ => .inr (.cleanupPeek stack)
  | .halt =>
      .load (fun _ => default) .halt





































































end

end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_UnaryPowerMacro
section
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM






























noncomputable def unaryPowerCostPolynomial
    (accumulator multiplier : Polynomial Nat) : Nat → Polynomial Nat
  | 0 => 0
  | d + 1 =>
      accumulator * (2 * multiplier + 3) + 2 + accumulator * multiplier + 1 +
        unaryPowerCostPolynomial (accumulator * multiplier) multiplier d



/-- Exact running-time polynomial for evaluation of the simple majorant
`C * (n + 1)^d`. -/
noncomputable def simpleMajorantEvalCostPolynomial
    (p : Polynomial Nat) : Polynomial Nat :=
  unaryPowerCostPolynomial (Polynomial.C (polyCoeffSum p))
    (Polynomial.X + 1) p.natDegree







end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_FullInputPreprocessor
section
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM



open Lax759944.BinaryWordEncoding

noncomputable section























































































noncomputable def simulationWidthPolynomial (p : Polynomial Nat) :
    Polynomial Nat := polynomialSimpleMajorant p + 1



noncomputable def fullInputCostPolynomial (p : Polynomial Nat) :
    Polynomial Nat :=
  let w := simulationWidthPolynomial p
  (4 * X + simpleMajorantEvalCostPolynomial p + 5) + 1 +
  (2 * w + 3 + (X * (2 * w + 4) + 2)) + 1 +
  (X + 2 * w + 5) +
  (1 + (X + 1) * (3 * w + 5) + 1) +
  ((X + 1) * (w + 1) + 4) +
  (3 * w + (X + 1) + 5)






end

end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_StackGrowthBounds
section
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

namespace Lax759944Proofs.RamToTM



def stmtPushCount {K Λ σ : Type} {Γ : K → Type} :
    TM2.Stmt Γ Λ σ → Nat
  | .push _ _ q => stmtPushCount q + 1
  | .peek _ _ q => stmtPushCount q
  | .pop _ _ q => stmtPushCount q
  | .load _ q => stmtPushCount q
  | .branch _ q₁ q₂ => max (stmtPushCount q₁) (stmtPushCount q₂)
  | .goto _ | .halt => 0



def programPushBound {K Λ σ : Type} {Γ : K → Type}
    [Fintype Λ] (program : Λ → TM2.Stmt Γ Λ σ) : Nat :=
  ∑ label : Λ, stmtPushCount (program label)







end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_CombinedInterpreter
section
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode
open Lax759944.BinaryWordEncoding

noncomputable section

abbrev MiddleLabel (p : Program) (N : Nat) :=
  Sum (FiniteInterpreterLabel p N) OutputAdapterLabel

def middleProgram (p : Program) (N : Nat)
    (hbound : programArgumentBound p <= N) : MiddleLabel p N →
    TM2.Stmt WrapperAlphabet (MiddleLabel p N) (WrapperState N)
  | .inl (.control .stopped) => .goto fun _ => .inr .initializeState
  | .inl label => liftCoreStmt (finiteInterpreterProgram p N hbound label)
  | .inr label => outputAdapterProgram label





































end

end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax759944Proofs_CellToMicrocode
section
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

/-!
Translation from the current cell-to-cell RAM to the proof-internal
accumulator microcode. Each instruction occupies three slots. All addresses
and the word width are preserved: no scratch memory is reserved. Only the
microcode accumulator, represented by a Turing work tape, is additional.
-/

namespace Lax759944Proofs.CellToMicrocode

abbrev Block := Microcode.Instr × Microcode.Instr × Microcode.Instr

def lower : Lax759944Proofs.Legacy.Ram.Instr → Block
  | .set a n => (.load (.lit n), .store a, .load (.lit 0))
  | .load a b => (.load (.ind b), .store a, .load (.lit 0))
  | .store a b => (.load (.mem b), .storeInd a, .load (.lit 0))
  | .add a b c => (.load (.mem b), .add (.mem c), .store a)
  | .sub a b c => (.load (.mem b), .sub (.mem c), .store a)
  | .mul a b c => (.load (.mem b), .mul (.mem c), .store a)
  | .div a b c => (.load (.mem b), .div (.mem c), .store a)
  | .and a b c => (.load (.mem b), .and (.mem c), .store a)
  | .not a b => (.load (.mem b), .compl (.lit 0), .store a)
  | .shiftl a b c => (.load (.mem b), .shiftl (.mem c), .store a)
  | .jump target => (.load (.lit 0), .load (.lit 0), .jump (3 * target))
  | .jzero a target => (.load (.mem a), .load (.mem a), .jzero (3 * target))
  | .halt => (.halt, .halt, .halt)
  | .read a => (.read a, .load (.lit 0), .load (.lit 0))
  | .write a => (.write (.mem a), .load (.lit 0), .load (.lit 0))

def block (i : Lax759944Proofs.Legacy.Ram.Instr) : Microcode.Program :=
  [(lower i).1, (lower i).2.1, (lower i).2.2]

def compile (p : Lax759944Proofs.Legacy.Ram.Program) : Microcode.Program := p.flatMap block





























end Lax759944Proofs.CellToMicrocode

end

-- Solutions.RAM_Lax759944Proofs_RamToTM_Polytime
section
-- Adapted from verified RAM-TM / word-RAM sources at the pinned commits.
-- Apache-2.0; see external-ram-tm/LICENSE and external-word-ram/word-ram/LICENSE.

set_option backward.isDefEq.respectTransparency false

namespace Lax759944Proofs.RamToTM

open Lax759944Proofs.Microcode
open Lax759944.BinaryWordEncoding

noncomputable section



noncomputable def terminalCostPolynomial
    (wordBound timeBound : Polynomial Nat) : Polynomial Nat :=
  let w := polynomialSimpleMajorant wordBound + 1
  2 * timeBound * (12 * w + 22) + 28 * w + 65

noncomputable def middleCostPolynomial
    (wordBound timeBound : Polynomial Nat) : Polynomial Nat :=
  coreSimulationPolynomial (polynomialSimpleMajorant wordBound) timeBound +
    terminalCostPolynomial wordBound timeBound + 1

noncomputable def initialCoreSizePolynomial
    (wordBound : Polynomial Nat) : Polynomial Nat :=
  let w := polynomialSimpleMajorant wordBound + 1
  w + (X + 1) * (w + 1) + 3

noncomputable def cleanupCostPolynomial (p : Program)
    (wordBound timeBound : Polynomial Nat) : Polynomial Nat :=
  let pushes := programPushBound
    (middleProgram p (programArgumentBound p) le_rfl)
  2 * (C 13 * (initialCoreSizePolynomial wordBound +
    C pushes * middleCostPolynomial wordBound timeBound)) + 13

noncomputable def outputCostPolynomial
    (wordBound timeBound : Polynomial Nat) : Polynomial Nat :=
  let w := polynomialSimpleMajorant wordBound + 1
  4 + timeBound * (3 * w + 3)

noncomputable def ramToTMTimePolynomial (p : Program)
    (wordBound timeBound : Polynomial Nat) : Polynomial Nat :=
  fullInputCostPolynomial wordBound + 2 +
    middleCostPolynomial wordBound timeBound +
    outputCostPolynomial wordBound timeBound +
    cleanupCostPolynomial p wordBound timeBound + 1



























end

end Lax759944Proofs.RamToTM

end

-- Solutions.RAM_Lax109476Proofs_RationalRounding
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


/-!
Computable rational rounding primitives with real error guarantees and grid
encoding bounds. These do not yet supply a RAM implementation.
-/

namespace Lax109476Proofs.RationalRounding

/-- Round to the grid with denominator `D`, towards minus infinity. -/
def roundDown (q : ℚ) (D : ℕ) : ℚ := (Int.floor (q * D) : ℚ) / D

/-- A rational upper approximation to a square root using integer square root. -/
def sqrtUpper (q : ℚ) (D : ℕ) : ℚ :=
  ((Nat.sqrt (Nat.ceil (q * (D : ℚ) ^ 2)) + 1 : ℕ) : ℚ) / D































end Lax109476Proofs.RationalRounding

end

-- Solutions.RAM_Lax109476Proofs_IntegerCertificates
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.




namespace Lax109476Proofs.IntegerCertificates

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate Lax109476.RecessionDirection
open IntegerEncoding

def coordinateCap (m n H : ℕ) : ℕ :=
  (2 * (m + n) + 2).factorial *
    ((2 * (m + n) + 2) * H ^ 2 + 1) ^ (2 * (m + n) + 2)



























end Lax109476Proofs.IntegerCertificates

end

-- Solutions.RAM_Lax109476Proofs_Relaxation
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.



namespace Lax109476Proofs.Relaxation

open Lax109476.LinearProgram Lax109476.FarkasCertificate
open Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates











def relaxationDenominator (m n H B : ℕ) : ℕ :=
  2 * (m * B + n * m * H * B + 1)















end Lax109476Proofs.Relaxation

end

-- Solutions.RAM_Lax109476Proofs_RationalSeparation
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.




namespace Lax109476Proofs.RationalSeparation

open Lax109476.RationalCertificates

def rowValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (c : Fin n → ℚ) (i : Fin m) : ℚ :=
  ∑ j, (A i j : ℚ) * c j

/-- Scan the finite rational inequalities in their stored order. -/
def firstViolation {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (c : Fin n → ℚ) : Option (Fin m) :=
  (List.finRange m).find? (fun i => decide (b i < rowValue A c i))





def rationalRow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (i : Fin m) : Fin n → ℚ :=
  fun j => A i j







end Lax109476Proofs.RationalSeparation

end

-- Solutions.RAM_Lax109476Proofs_EllipsoidRounding
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


/-!
Internal shape-rounding lemmas. Entrywise rounding needs a diagonal enlargement:
entrywise inequalities alone do not imply containment of ellipsoids.
-/

namespace Lax109476Proofs.EllipsoidRounding













/-- Round every rational entry down, then add a diagonal error allowance. -/
def roundedShape {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (D : ℕ) :
    Matrix (Fin n) (Fin n) ℚ :=
  (Matrix.of fun i j => RationalRounding.roundDown (A i j) D) + ((n : ℚ) / D) • 1

























end Lax109476Proofs.EllipsoidRounding

end

-- Solutions.RAM_Lax109476Proofs_EllipsoidBounds
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


/-! Internal conditioning and precision bounds for general central-cut shapes. -/

namespace Lax109476Proofs.EllipsoidBounds

open EllipsoidRounding



/-- The general central-cut shape uses only rational operations on its data. -/
def cutShape (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (a : Fin n → ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  ((n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1)) •
    (A - (2 / (((n : ℚ) + 1) * (a ⬝ᵥ (A *ᵥ a)))) •
      Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a))





























end Lax109476Proofs.EllipsoidBounds

end

-- Solutions.RAM_Lax109476Proofs_EllipsoidCenter
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


/-! Computable center updates and their error in the new ellipsoid's metric. -/

namespace Lax109476Proofs.EllipsoidCenter

open EllipsoidRounding EllipsoidBounds
open Lax109476.RationalCertificates





/-- Before grid rounding, the new center uses a rational upper square root. -/
def approximateCenter (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a c : Fin n → ℚ) (D : ℕ) : Fin n → ℚ :=
  c - (1 / (((n : ℚ) + 1) * RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D)) •
    (A *ᵥ a)

/-- The stored center is rounded onto the same rational grid as the shape. -/
def roundedCenter (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a c : Fin n → ℚ) (D : ℕ) : Fin n → ℚ :=
  fun i => RationalRounding.roundDown (approximateCenter n A a c D i) D













/-- The stored rational shape also includes the allowance for center displacement. -/
def roundedStepShape (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ)
    (a : Fin n → ℚ) (D : ℕ) (η : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  ((1 + η) ^ 2) • roundedShape (cutShape n A a) D







end Lax109476Proofs.EllipsoidCenter

end

-- Solutions.RAM_Lax109476Proofs_EllipsoidPrecision
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


/-! A uniform dyadic grid for both parts of the rational center update. -/

namespace Lax109476Proofs.EllipsoidPrecision

open EllipsoidRounding EllipsoidBounds EllipsoidCenter
open Lax109476.RationalCertificates

/-- This denominator has a linear bit length in the conditioning and accuracy exponents. -/
def gridDenominator (l s n : ℕ) : ℕ := 2 ^ (l + s + n + 3)















end Lax109476Proofs.EllipsoidPrecision

end

-- Solutions.RAM_Lax109476Proofs_EllipsoidIteration
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


/-! Conditioning and determinant shrinkage of the same rational stored update. -/

namespace Lax109476Proofs.EllipsoidIteration

open EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision
open Lax109476.RationalCertificates

/-- The per-step enlargement used by the uniform precision schedule. -/
def stepAccuracy (n : ℕ) : ℚ := 1 / (2 : ℚ) ^ (2 * n + 4)













end Lax109476Proofs.EllipsoidIteration

end

-- Solutions.RAM_Lax109476Proofs_EllipsoidSequence
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


/-!
A concrete sequence of rational stored ellipsoids. The cut normals are supplied
externally; no LP separation, stopping rule, certificate recovery, or RAM execution
is asserted here.
-/

namespace Lax109476Proofs.EllipsoidSequence

open EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision EllipsoidIteration
open Lax109476.RationalCertificates















/-- A polynomial number of steps suffices for a prescribed dyadic determinant threshold. -/
def thresholdSteps (n B : ℕ) : ℕ := 4 * (n + 1) * (B * n + 1)



end Lax109476Proofs.EllipsoidSequence

end

-- Solutions.RAM_Lax109476Proofs_EllipsoidSearch
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.




namespace Lax109476Proofs.EllipsoidSearch

open Lax109476.RationalCertificates
open RationalSeparation EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence

/-- Materialize every shape and center entry once per update. Subsequent
matrix operations read the stored arrays rather than recomputing entries. -/
def cacheState {n : ℕ} (state : Matrix (Fin n) (Fin n) ℚ × (Fin n → ℚ)) :
    Matrix (Fin n) (Fin n) ℚ × (Fin n → ℚ) :=
  let rows : Vector (Vector ℚ n) n := Vector.ofFn (fun i => Vector.ofFn (state.1 i))
  let center : Vector ℚ n := Vector.ofFn state.2
  ((fun i j => (rows.get i).get j), fun i => center.get i)



def fallbackNormal (n : ℕ) : Fin n → ℚ := fun j => if j.val = 0 then 1 else 0

/-- A nonzero integer violated row supplies the normal; a fixed nonzero
normal makes the trajectory total after success or a violated constant row. -/
def selectedNormal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (c : Fin n → ℚ) : Fin n → ℚ :=
  match firstViolation A b c with
  | none => fallbackNormal n
  | some i => if A i = 0 then fallbackNormal n else rationalRow A i

def nextState {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (k : ℕ) (old : Matrix (Fin n) (Fin n) ℚ × (Fin n → ℚ)) :
    Matrix (Fin n) (Fin n) ℚ × (Fin n → ℚ) :=
    let a := selectedNormal A b old.2
    let D := gridDenominator (2 * k + 2) (2 * n + 4) n
    cacheState
      (roundedStepShape n old.1 a D (stepAccuracy n), roundedCenter n old.1 a old.2 D)















/-- Advance the stored state once per failed test, keeping the iteration
index synchronized with the precision schedule. -/
def scanStates {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ) :
    ℕ → ℕ → (Matrix (Fin n) (Fin n) ℚ × (Fin n → ℚ)) → Option ℕ
  | _, 0, _ => none
  | start, count + 1, state =>
    if firstViolation A b state.2 = none then some start
    else scanStates A b (start + 1) count (nextState A b start state)



/-- Inspect the bounded sequence of centers with exact rational comparisons.
The computation allocates no list of the entire worst-case iteration budget. -/
def findIteration {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℚ)
    (K : ℕ) : Option ℕ :=
  scanStates A b 0 (K + 1) (1, 0)











end Lax109476Proofs.EllipsoidSearch

end

-- Solutions.RAM_Lax109476Proofs_NormalizedFeasibility
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.




namespace Lax109476Proofs.NormalizedFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates Relaxation

def outerScale (n B : ℕ) : ℕ := 4 * (n + 1) * (B + 1)

def normalizedMatrix {m n : ℕ} (P : Program ℤ m n) (R : ℕ) :
    Matrix (Fin (m + n)) (Fin n) ℤ :=
  Fin.addCases (fun i j => (R : ℤ) * P.A i j)
    (fun k j => if k = j then -(R : ℤ) else 0)

def normalizedBound {m n : ℕ} (P : Program ℤ m n) (ε : ℚ) : Fin (m + n) → ℚ :=
  Fin.addCases (fun i => (P.b i : ℚ) + ε) (fun _ => ε)











def precisionDenominator (m n H : ℕ) : ℕ :=
  relaxationDenominator m n H (coordinateCap m n H)

def ballDenominator (m n H : ℕ) : ℕ :=
  precisionDenominator m n H * (n * H + 1) * outerScale n (coordinateCap m n H)

def ballExponent (m n H : ℕ) : ℕ := Nat.size (ballDenominator m n H)













end Lax109476Proofs.NormalizedFeasibility

end

-- Solutions.RAM_Lax109476Proofs_IntegerFeasibilityDecision
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.




namespace Lax109476Proofs.IntegerFeasibilityDecision

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates Relaxation NormalizedFeasibility
open EllipsoidSearch EllipsoidSequence

def iterationResult {m n : ℕ} (P : Program ℤ m n) (H : ℕ) : Option ℕ :=
  findIteration (normalizedMatrix P (outerScale n (coordinateCap m n H)))
    (normalizedBound P (1 / (precisionDenominator m n H : ℚ)))
    (thresholdSteps n (ballExponent m n H))

/-- A computable exact feasibility test using rounded rational ellipsoid steps.
This definition alone makes no claim about registered RAM execution. -/
def feasible {m n : ℕ} (P : Program ℤ m n) (H : ℕ) : Bool := (iterationResult P H).isSome







end Lax109476Proofs.IntegerFeasibilityDecision

end

-- Solutions.RAM_Lax109476Proofs_FeasibilityPadding
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.




namespace Lax109476Proofs.FeasibilityPadding

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding

/-- Two nonnegative dummy variables, each constrained to be at most zero,
allow the same ellipsoid implementation to handle all input dimensions. -/
def pad {K : Type} [Zero K] [One K] {m n : ℕ} (P : Program K m n) :
    Program K (m + 2) (n + 2) where
  A := Fin.addCases (fun i => Fin.addCases (P.A i) (fun _ => 0))
    (fun k => Fin.addCases (fun _ => 0) (fun j => if k = j then 1 else 0))
  b := Fin.addCases P.b (fun _ => 0)
  c := Fin.addCases P.c (fun _ => 0)











def feasible {m n : ℕ} (P : Program ℤ m n) (H : ℕ) : Bool :=
  IntegerFeasibilityDecision.feasible (pad P) H



end Lax109476Proofs.FeasibilityPadding

end

-- Solutions.RAM_Lax109476Proofs_RationalFeasibilityDecision
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.




namespace Lax109476Proofs.RationalFeasibilityDecision

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open IntegerEncoding EncodingSize NormalizedFeasibility EllipsoidSequence





def sizeParameter {m n : ℕ} (P : Program ℚ m n) : ℕ := bitSize (encodeProgram P) + 4

/-- Total, computable feasibility decision by exact rational ellipsoid updates.
Its mathematical correctness does not assert a RAM execution theorem. -/
def feasible {m n : ℕ} (P : Program ℚ m n) : Bool :=
  FeasibilityPadding.feasible (integerProgram P) (2 ^ (2 * sizeParameter P))







end Lax109476Proofs.RationalFeasibilityDecision

end

-- Solutions.RAM_Lax109476Proofs_RamRational
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRational

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamArithmetic

def fractionValue (s n d : ℕ) : ℚ := if s = 1 then -(n : ℚ) / d else (n : ℚ) / d

































end Lax109476Proofs.RamRational

end

-- Solutions.RAM_Lax109476Proofs_RationalArithmeticBounds
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.




namespace Lax109476Proofs.RationalArithmeticBounds

open RationalSizeBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding

def Height (q : ℚ) (B : ℕ) : Prop := q.num.natAbs ≤ B ∧ q.den ≤ B

























end Lax109476Proofs.RationalArithmeticBounds

end

-- Solutions.RAM_Lax109476Proofs_RamCenterCoordinate
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCenterCoordinate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RationalArithmeticBounds



def centerCap (M : ℕ) : ℕ := 2 * (M + 1) ^ 4 + 1











end Lax109476Proofs.RamCenterCoordinate

end

-- Solutions.RAM_Lax109476Proofs_RamCopy
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCopy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RationalArithmeticBounds

def suffixes : List String := [".s", ".n", ".d"]
def Disjoint (a b : String) : Prop := ∀ s ∈ suffixes, ∀ t ∈ suffixes, a ++ s ≠ b ++ t



























end Lax109476Proofs.RamCopy

end

-- Solutions.RAM_Lax109476Proofs_RamDotProduct
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.




namespace Lax109476Proofs.RamDotProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RationalArithmeticBounds







def cap (n H : ℕ) : ℕ := (2 * (H * H)) ^ (n + 1)



































end Lax109476Proofs.RamDotProduct

end

-- Solutions.RAM_Lax109476Proofs_RamShapeCoordinate
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamShapeCoordinate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFractionInterface RationalArithmeticBounds















def shapeCap (M : ℕ) : ℕ := 8 * (M + 1) ^ 8





























end Lax109476Proofs.RamShapeCoordinate

end

-- Solutions.RAM_Lax109476Proofs_RamEllipsoidForm
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.




namespace Lax109476Proofs.RamEllipsoidForm

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamDotProduct RamMatrixRows RamMatrixVector
open RationalArithmeticBounds

def FormOutput (q : ℚ) (σ : Env) : Prop :=
  fractionValue (σ.vars "ell.form.s") (σ.vars "ell.form.n") (σ.vars "ell.form.d") = q ∧
    σ.vars "ell.form.n" = q.num.natAbs ∧ σ.vars "ell.form.d" = q.den ∧ σ.vars "ell.form.s" ≤ 1





def formHeight (n H : ℕ) : ℕ := cap n (cap n H)











end Lax109476Proofs.RamEllipsoidForm

end

-- Solutions.RAM_Lax109476Proofs_RamEllipsoidCoefficients
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamEllipsoidCoefficients

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamEllipsoidScalars RamEllipsoidForm
open RationalArithmeticBounds













def coefficients (n : ℕ) (q : ℚ) (D E : ℕ) : List ℚ :=
  [(n : ℚ) ^ 2 / ((n : ℚ) ^ 2 - 1), 2 / (((n : ℚ) + 1) * q),
    1 / (((n : ℚ) + 1) * RationalRounding.sqrtUpper q D),
    (1 + 1 / (E : ℚ)) ^ 2, (n : ℚ) / D]





def ScalarInput (n : ℕ) (q : ℚ) (D E : ℕ) (σ : Env) : Prop :=
  FormOutput q σ ∧ σ.vars "vec.n" = n ∧ σ.vars "grid.D" = D ∧ σ.vars "ell.epsden" = E









def coefficientCap (M : ℕ) : ℕ := 4 * (M + 1) ^ 4















end Lax109476Proofs.RamEllipsoidCoefficients

end

-- Solutions.RAM_Lax109476Proofs_RamEllipsoidStep
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.




namespace Lax109476Proofs.RamEllipsoidStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RationalArithmeticBounds
open RamEllipsoidUpdate RamEllipsoidPrecision RamEllipsoidCoefficients
open RamEllipsoidScalars RamEllipsoidForm RamMatrixVector RamMatrixRows RamDotProduct RamMatrixStorage















def formCost (n H : ℕ) : ℕ :=
  33 * n + 18 + (((4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 21 + 4) + 4) * n + 8) +
    (((144 * (formHeight n H).size + 210 + 4) * n + 12) + 6)

def updateCost (n M : ℕ) : ℕ :=
  (33 * n + 18 + ((180 * (RamCenterCoordinate.centerCap M).size + 318 + 4 + 4) * n + 6)) +
    (33 * (n * n) + 26 + ((468 * (RamShapeCoordinate.shapeCap M).size + 690 + 4 + 4) * (n * n) + 10))

def stepCost (n H M : ℕ) : ℕ := formCost n H + 20 + (582 * M.size + 876) + updateCost n (coefficientCap M)
















 

end Lax109476Proofs.RamEllipsoidStep

end

-- Solutions.RAM_Lax109476Proofs_RamEquationData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamEquationData

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays IntegerEncoding




def Data {m n : ℕ} (P : Program ℤ m n) (σ : Env) : Prop :=
  Represents "system.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ ∧
    Represents "system.b" (List.ofFn (rationalProgram P).b) σ ∧
    σ.vars "system.m" = m ∧ σ.vars "system.n" = n







end Lax109476Proofs.RamEquationData

end

-- Solutions.RAM_Lax109476Proofs_RamCertificateDecision
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamCertificateDecision

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RationalArithmeticBounds IntegerEncoding










def Input {r s : ℕ} (F : Program ℤ r s) (source target : String) (σ : Env) : Prop :=
  RamEquationData.Data F (prefixedView source σ) ∧
    Extents (target ++ "lp.A") (r * s) σ ∧ Extents (target ++ "lp.b") r σ ∧ Extents (target ++ "lp.c") s σ ∧
    Extents (target ++ "int.A") (r * s) σ ∧ Extents (target ++ "int.b") r σ ∧ Extents (target ++ "int.c") s σ ∧
    RamFeasibilityQuery.Workspace r s (prefixedView target σ)












end Lax109476Proofs.RamCertificateDecision

end



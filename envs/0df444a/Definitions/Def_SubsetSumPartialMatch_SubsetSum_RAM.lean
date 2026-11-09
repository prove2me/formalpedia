-- Prove2me | Definitions.Def_SubsetSumPartialMatch_SubsetSum_RAM
-- name    : SubsetSumPartialMatch_SubsetSum_RAM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:29.908363+00:00
-- url     : https://prove2.me/theorems/0da7481e-0bc2-42fb-bbd7-ba8ada423262
-- title:
--   Logarithmic-cost randomized random access machine
-- statement:
--   A **program** is a finite list of instructions acting on a memory $m:\mathbb N\to\mathbb Z$ of unbounded signed integers: load a constant, add, subtract, multiply, Euclidean quotient and remainder, indirect load and store, unconditional jump, jump if a cell is positive, and a coin toss that writes the next bit of a random tape $\omega\in\{0,1\}^{\mathbb N}$. The machine halts when the program counter passes the end of the list.
--
--   Costs are defined from the instructions and from the operands actually met during the run. Writing $|v|_2$ for the bit length of an integer $v$ (binary digits of its absolute value plus a sign bit), an addition or subtraction is charged the lengths of its two operands and of its addresses; a multiplication, quotient or remainder is charged the schoolbook product $|x|_2\,|y|_2$ plus the lengths of its addresses; an indirect access is charged the length of the computed address and of the word moved; every instruction is charged at least $1$. This is the logarithmic cost criterion of Cook and Reckhow (*Time-bounded random access machines*, JCSS 1973, https://doi.org/10.1016/S0022-0000(73)80029-7), with a coin-toss instruction added, and it is the meaning given to "bit operations" throughout the mission: a large integer is never handled at unit cost.
--
--   Input and output are word lists: cell $0$ holds the number of words and cells $1,2,\dots$ hold the words, in both directions. A program is **deterministic** if it contains no coin toss. The random tape has the law of independent fair bits, built as a countable product measure.
--
--   **Formalization Note** The model has no instruction that refers to the problem being solved, and no advice: the program is finite and the only initial data are the input words. Addresses are absolute values of integers and quotient by zero returns $0$; both conventions are total, charged like any other instruction, and give no extra power. Bit shifts are omitted because a multiplication by a power of two does the same work at a cost at least as high. The auxiliary predicate `Enumerates` says a list lists a set without repetition.
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 9, §2 ("the running times of our algorithms are measured in bit operations"); the machine itself is the standard log-cost RAM of Cook & Reckhow, JCSS 1973

import Mathlib

namespace SubsetSumPartialMatch.SubsetSum

/-- Length in bits of a signed integer: the binary digits of `|v|` plus one sign bit. So
`wordLen 0 = 1`. Every cost charged by the machine below is built from this length. -/
def wordLen (v : ℤ) : ℕ := Nat.size v.natAbs + 1

/-- Total bit length of a list of machine words. -/
def wordsLen (ws : List ℤ) : ℕ := (ws.map wordLen).sum

/-- Instructions of the logarithmic-cost random access machine. Operands `d a b c s` are direct
cell addresses, `t` is a program location. `load` and `store` are the indirect accesses, `rand`
writes one fresh fair bit. There is no instruction that consults the problem being solved. -/
inductive Instr where
  /-- `mem[d] := v` -/
  | const (d : ℕ) (v : ℤ)
  /-- `mem[d] := mem[a] + mem[b]` -/
  | add (d a b : ℕ)
  /-- `mem[d] := mem[a] - mem[b]` -/
  | sub (d a b : ℕ)
  /-- `mem[d] := mem[a] * mem[b]` -/
  | mul (d a b : ℕ)
  /-- `mem[d] := mem[a] / mem[b]` (Euclidean quotient; `0` when `mem[b] = 0`) -/
  | div (d a b : ℕ)
  /-- `mem[d] := mem[a] % mem[b]` (Euclidean remainder; `mem[a]` when `mem[b] = 0`) -/
  | mod (d a b : ℕ)
  /-- `mem[d] := mem[|mem[a]|]` -/
  | load (d a : ℕ)
  /-- `mem[|mem[a]|] := mem[s]` -/
  | store (a s : ℕ)
  /-- go to location `t` -/
  | jump (t : ℕ)
  /-- go to location `t` if `mem[c] > 0` -/
  | jumpPos (c t : ℕ)
  /-- `mem[d] :=` the next bit of the random tape -/
  | rand (d : ℕ)
  deriving DecidableEq

/-- A program is a finite instruction list; it is fixed before any input is seen, and any
constants it contains are part of this finite text. -/
abbrev Program := List Instr

/-- A machine configuration: program counter, memory, number of random bits consumed, and the
bit operations charged so far. -/
structure Config where
  pc : ℕ
  mem : ℕ → ℤ
  coins : ℕ
  cost : ℕ

/-- Bit length of a direct address. -/
def adrLen (d : ℕ) : ℕ := wordLen (d : ℤ)

/-- Move to the next instruction, writing `v` to cell `d` and charging `k`. -/
def Config.write (c : Config) (d : ℕ) (v : ℤ) (k : ℕ) : Config :=
  { c with pc := c.pc + 1, mem := Function.update c.mem d v, cost := c.cost + k }

/-- Execute one instruction on the random tape `ω`. Additive instructions are charged the lengths
of their operands and addresses; `mul`, `div`, `mod` are charged the schoolbook product of the
operand lengths; indirect accesses are charged the length of the computed address and of the word
moved. Every instruction is charged at least `1`. -/
def exec (i : Instr) (ω : ℕ → Bool) (c : Config) : Config :=
  match i with
  | .const d v => c.write d v (1 + adrLen d + wordLen v)
  | .add d a b =>
      c.write d (c.mem a + c.mem b)
        (1 + adrLen d + adrLen a + adrLen b + wordLen (c.mem a) + wordLen (c.mem b))
  | .sub d a b =>
      c.write d (c.mem a - c.mem b)
        (1 + adrLen d + adrLen a + adrLen b + wordLen (c.mem a) + wordLen (c.mem b))
  | .mul d a b =>
      c.write d (c.mem a * c.mem b)
        (1 + adrLen d + adrLen a + adrLen b + wordLen (c.mem a) * wordLen (c.mem b))
  | .div d a b =>
      c.write d (c.mem a / c.mem b)
        (1 + adrLen d + adrLen a + adrLen b + wordLen (c.mem a) * wordLen (c.mem b))
  | .mod d a b =>
      c.write d (c.mem a % c.mem b)
        (1 + adrLen d + adrLen a + adrLen b + wordLen (c.mem a) * wordLen (c.mem b))
  | .load d a =>
      c.write d (c.mem (c.mem a).natAbs)
        (1 + adrLen d + adrLen a + wordLen (c.mem a) + wordLen (c.mem (c.mem a).natAbs))
  | .store a s =>
      c.write (c.mem a).natAbs (c.mem s)
        (1 + adrLen a + adrLen s + wordLen (c.mem a) + wordLen (c.mem s))
  | .jump t => { c with pc := t, cost := c.cost + 1 }
  | .jumpPos b t =>
      { c with
        pc := if 0 < c.mem b then t else c.pc + 1
        cost := c.cost + (1 + adrLen b + wordLen (c.mem b)) }
  | .rand d =>
      { c.write d (if ω c.coins then 1 else 0) (2 + adrLen d) with coins := c.coins + 1 }

/-- One machine step. A configuration whose program counter is past the end of the program is
halted and does not change. -/
def step (P : Program) (ω : ℕ → Bool) (c : Config) : Config :=
  match P[c.pc]? with
  | some i => exec i ω c
  | none => c

/-- The machine has halted. -/
def Halted (P : Program) (c : Config) : Prop := P.length ≤ c.pc

/-- Input convention: cell `0` holds the number of input words and cells `1, 2, …` hold the
words; all other cells are `0`. The same layout is read back as the output. -/
def initMem (input : List ℤ) : ℕ → ℤ
  | 0 => input.length
  | i + 1 => input.getD i 0

/-- The configuration in which every run starts. -/
def initConfig (input : List ℤ) : Config := ⟨0, initMem input, 0, 0⟩

/-- The configuration after `t` steps. -/
def runFor (P : Program) (ω : ℕ → Bool) (input : List ℤ) (t : ℕ) : Config :=
  (step P ω)^[t] (initConfig input)

/-- The output words of a configuration: cell `0` gives their number, cells `1, 2, …` the words. -/
def outputOf (c : Config) : List ℤ :=
  (List.range (c.mem 0).toNat).map fun i => c.mem (i + 1)

/-- On tape `ω` and this input, the run halts and its output is `out`. -/
def Outputs (P : Program) (ω : ℕ → Bool) (input out : List ℤ) : Prop :=
  ∃ t, Halted P (runFor P ω input t) ∧ outputOf (runFor P ω input t) = out

/-- On tape `ω` and this input, the run halts with at most `T` charged bit operations. -/
def CostWithin (P : Program) (ω : ℕ → Bool) (input : List ℤ) (T : ℝ) : Prop :=
  ∃ t, Halted P (runFor P ω input t) ∧ ((runFor P ω input t).cost : ℝ) ≤ T

/-- A deterministic program never executes a coin toss, because it does not contain one. -/
def Deterministic (P : Program) : Prop := ∀ d, Instr.rand d ∉ P

/-- The tape on which deterministic programs are run; they never read it. -/
def blankTape : ℕ → Bool := fun _ => false

/-- `L` lists the set `S` without repetition. -/
def Enumerates {X : Type} (L : List X) (S : Set X) : Prop := L.Nodup ∧ ∀ x, x ∈ L ↔ x ∈ S

/-- The law of one fair bit. -/
noncomputable def coinMeasure : MeasureTheory.Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

instance : MeasureTheory.IsProbabilityMeasure coinMeasure := by
  unfold coinMeasure; infer_instance

/-- The law of the random tape: independent fair bits. -/
noncomputable def tapeMeasure : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi fun _ => coinMeasure

end SubsetSumPartialMatch.SubsetSum



-- Prove2me | Definitions.Def_DynConnWC_Program
-- name    : DynConnWC_Program
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:30:31.874759+00:00
-- url     : https://prove2.me/theorems/2d0221d2-97d7-4ecd-829b-31d5c0627727
-- title:
--   The online randomized word RAM
-- statement:
--   A machine with word size $W$ has a memory of $W$-bit words, all zero initially, and a program counter. Its instructions are: load the constant $1$; addition, subtraction, multiplication, unsigned division and remainder, bitwise AND, OR and XOR, and shifts, all modulo $2^W$; indirect load and store; a branch on a negative word; a jump; `read`, which stores the next input word; `write`, which appends a word to the output; `rand`, which stores the next word of the random tape; and `halt`. Every executed instruction is one step.
--
--   The machine is online: the $k$-th executed `read` stores the $k$-th input word, and the all-ones word once the input is exhausted, so a run sees an input word only when it reads it. The $c$-th executed `rand` stores the word $\omega(c)$ of the tape $\omega$.
--
--   This is the model behind the paper's bounds: time is measured in word operations and space in words.
--
--   **Formalization Note** Division by zero gives $0$ and the remainder modulo zero gives the dividend (the `BitVec` conventions). The source says "a word RAM" without an instruction list. Bit operations are included because the cutset summaries are XORs (A.1) and field products are carry-less multiplications (A.4). `touched` lists the memory cells an instruction accesses, which is how space is measured.
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), §2, p.4 (PDF 5); Appendix A.1, p.27; A.4, p.30

import Mathlib

set_option autoImplicit false

namespace DynConnWC

/-! # The online randomized word RAM

King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027
submission, sha256 9d16c13e…), §2, p.4: "We use a word RAM with words of Θ(log n) bits. Time is
measured in word operations and space in words. Time bounds on operations are worst-case unless
stated otherwise." §2, p.4: "Probabilities are over the algorithm's randomness."

**Formalization Note.** A machine with word size `W` has memory `ℕ → BitVec W`, all zero
initially, and a program counter. Operands `i j k` are direct addresses fixed in the program;
`load`/`store` are indirect accesses (address = the unsigned value of a word). Arithmetic is
modulo `2^W`; `udiv x 0 = 0` and `umod x 0 = x` (the `BitVec` conventions); shift amounts are read
unsigned. `bltz` branches when a word is negative as a signed word (top bit set). Every executed
instruction costs one step. The machine is **online**: the `k`-th executed `read` stores the
`k`-th input word (the all-ones word once the input is exhausted), so a run never sees an input
word before it reads it, and `write` appends a word to the output. It is **randomized**: the
`c`-th executed `rand` (counting from `0`) stores the word `ω c` of the random tape
`ω : ℕ → Fin (2^W)`. A program halts at `halt` or when the program counter leaves the program.
`touched` lists the memory cells an instruction accesses (its direct operands and, for
`load`/`store`, the indirect address); space is measured by the cells touched. -/

/-- The instruction set. `[i]` denotes memory cell `i`. -/
inductive Instr where
  /-- `[i] := 1` -/
  | one (i : ℕ)
  /-- `[i] := [j] + [k]` -/
  | add (i j k : ℕ)
  /-- `[i] := [j] - [k]` -/
  | sub (i j k : ℕ)
  /-- `[i] := [j] * [k]` -/
  | mul (i j k : ℕ)
  /-- `[i] := [j] / [k]` (unsigned) -/
  | udiv (i j k : ℕ)
  /-- `[i] := [j] mod [k]` (unsigned) -/
  | umod (i j k : ℕ)
  /-- bitwise and -/
  | band (i j k : ℕ)
  /-- bitwise or -/
  | bor (i j k : ℕ)
  /-- bitwise xor -/
  | bxor (i j k : ℕ)
  /-- `[i] := [j] <<< [k]` -/
  | shl (i j k : ℕ)
  /-- `[i] := [j] >>> [k]` (logical) -/
  | shr (i j k : ℕ)
  /-- `[i] := [[j]]` -/
  | load (i j : ℕ)
  /-- `[[i]] := [j]` -/
  | store (i j : ℕ)
  /-- jump to `l` if `[i] < 0` as a signed word -/
  | bltz (i l : ℕ)
  /-- jump to `l` -/
  | jmp (l : ℕ)
  /-- `[i] :=` the next input word -/
  | read (i : ℕ)
  /-- append `[i]` to the output -/
  | write (i : ℕ)
  /-- `[i] :=` the next word of the random tape -/
  | rand (i : ℕ)
  | halt
  deriving DecidableEq

/-- A program is a finite list of instructions; execution starts at index `0`. -/
abbrev Program := List Instr

/-- A configuration of the machine with word size `W`: program counter, memory, the number of
`read` and `rand` instructions executed so far, and the output written so far. -/
structure Config (W : ℕ) where
  pc : ℕ
  mem : ℕ → BitVec W
  reads : ℕ
  rands : ℕ
  output : List ℕ

namespace Config

variable {W : ℕ}

/-- Write `v` into cell `a` and advance the program counter. -/
def assign (c : Config W) (a : ℕ) (v : BitVec W) : Config W :=
  { c with pc := c.pc + 1, mem := Function.update c.mem a v }

end Config

/-- One step of program `P` on input words `inp` and random tape `ω`. A halted configuration is
left unchanged. -/
def step {W : ℕ} (P : Program) (inp : List ℕ) (ω : ℕ → Fin (2 ^ W)) (c : Config W) : Config W :=
  match P[c.pc]? with
  | none => c
  | some Instr.halt => c
  | some (Instr.one i) => c.assign i 1
  | some (Instr.add i j k) => c.assign i (c.mem j + c.mem k)
  | some (Instr.sub i j k) => c.assign i (c.mem j - c.mem k)
  | some (Instr.mul i j k) => c.assign i (c.mem j * c.mem k)
  | some (Instr.udiv i j k) => c.assign i (BitVec.udiv (c.mem j) (c.mem k))
  | some (Instr.umod i j k) => c.assign i (BitVec.umod (c.mem j) (c.mem k))
  | some (Instr.band i j k) => c.assign i (c.mem j &&& c.mem k)
  | some (Instr.bor i j k) => c.assign i (c.mem j ||| c.mem k)
  | some (Instr.bxor i j k) => c.assign i (c.mem j ^^^ c.mem k)
  | some (Instr.shl i j k) => c.assign i (c.mem j <<< (c.mem k).toNat)
  | some (Instr.shr i j k) => c.assign i (c.mem j >>> (c.mem k).toNat)
  | some (Instr.load i j) => c.assign i (c.mem (c.mem j).toNat)
  | some (Instr.store i j) => c.assign (c.mem i).toNat (c.mem j)
  | some (Instr.bltz i l) =>
      if (c.mem i).msb then { c with pc := l } else { c with pc := c.pc + 1 }
  | some (Instr.jmp l) => { c with pc := l }
  | some (Instr.read i) =>
      { c.assign i (match inp[c.reads]? with
                    | none => BitVec.allOnes W
                    | some x => BitVec.ofNat W x) with reads := c.reads + 1 }
  | some (Instr.write i) => { c with pc := c.pc + 1, output := c.output ++ [(c.mem i).toNat] }
  | some (Instr.rand i) => { c.assign i (BitVec.ofFin (ω c.rands)) with rands := c.rands + 1 }

/-- The memory cells accessed by the instruction about to be executed in configuration `c`. -/
def touched {W : ℕ} (P : Program) (c : Config W) : List ℕ :=
  match P[c.pc]? with
  | some (Instr.one i) => [i]
  | some (Instr.add i j k) => [i, j, k]
  | some (Instr.sub i j k) => [i, j, k]
  | some (Instr.mul i j k) => [i, j, k]
  | some (Instr.udiv i j k) => [i, j, k]
  | some (Instr.umod i j k) => [i, j, k]
  | some (Instr.band i j k) => [i, j, k]
  | some (Instr.bor i j k) => [i, j, k]
  | some (Instr.bxor i j k) => [i, j, k]
  | some (Instr.shl i j k) => [i, j, k]
  | some (Instr.shr i j k) => [i, j, k]
  | some (Instr.load i j) => [i, j, (c.mem j).toNat]
  | some (Instr.store i j) => [i, j, (c.mem i).toNat]
  | some (Instr.bltz i _) => [i]
  | some (Instr.read i) => [i]
  | some (Instr.write i) => [i]
  | some (Instr.rand i) => [i]
  | _ => []

/-- The initial configuration: program counter `0`, all memory zero, nothing read or written. -/
def initConfig (W : ℕ) : Config W := ⟨0, fun _ => 0, 0, 0, []⟩

/-- The configuration after `t` steps of `P` on input words `inp` and tape `ω`. -/
def conf (W : ℕ) (P : Program) (inp : List ℕ) (ω : ℕ → Fin (2 ^ W)) (t : ℕ) : Config W :=
  (step P inp ω)^[t] (initConfig W)

/-- `ReadsAt W P inp ω k t`: the `k`-th executed `read` instruction (counting from `1`) is the
instruction executed at step `t`, i.e. in the configuration reached after `t` steps. -/
def ReadsAt (W : ℕ) (P : Program) (inp : List ℕ) (ω : ℕ → Fin (2 ^ W)) (k t : ℕ) : Prop :=
  (∃ i, P[(conf W P inp ω t).pc]? = some (Instr.read i)) ∧ (conf W P inp ω t).reads + 1 = k

open Classical in
/-- The step at which the `k`-th `read` is executed (`none` if the run never executes it). The
step index equals the number of steps executed before it. -/
noncomputable def readStep (W : ℕ) (P : Program) (inp : List ℕ) (ω : ℕ → Fin (2 ^ W)) (k : ℕ) :
    Option ℕ :=
  if h : ∃ t, ReadsAt W P inp ω k t then some (Nat.find h) else none

/-- The words written by the steps `t₁, …, t₂ - 1` (for `t₁ ≤ t₂`). -/
def outputBetween (W : ℕ) (P : Program) (inp : List ℕ) (ω : ℕ → Fin (2 ^ W)) (t₁ t₂ : ℕ) :
    List ℕ :=
  (conf W P inp ω t₂).output.drop (conf W P inp ω t₁).output.length

/-- The memory cells accessed by the steps `t₁, …, t₂ - 1`. -/
def touchedBetween (W : ℕ) (P : Program) (inp : List ℕ) (ω : ℕ → Fin (2 ^ W)) (t₁ t₂ : ℕ) :
    Set ℕ :=
  {a | ∃ s, t₁ ≤ s ∧ s < t₂ ∧ a ∈ touched P (conf W P inp ω s)}

end DynConnWC



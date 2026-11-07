-- Prove2me | Definitions.Def_DynSetCover_DRAM
-- name    : DynSetCover_DRAM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:52.438108+00:00
-- url     : https://prove2.me/theorems/4bc97633-4e42-4167-84c3-39ee66a31c57
-- title:
--   §7 — the online word-RAM: instructions, configurations, steps and reads
-- statement:
--   The machine model of §7 is a **word-RAM** with $W$-bit words and constant-time arithmetic, integer division, comparisons, bit operations and table access. A configuration holds a program counter, a memory $\mathbb N\to\{0,1\}^W$ (all zero initially), the remaining input, the output written so far, the number of reads executed, and the set of memory cells written. The instructions are
--   1. $[i]:=1$; $[i]:=[j]\circ[k]$ for $\circ\in\{+,-,\times,\div,\bmod,\text{and},\text{or},\text{xor},\ll,\gg\}$ (modulo $2^W$; $x\div0=0$, $x\bmod 0=x$);
--   2. indirect access $[i]:=[[j]]$ and $[[i]]:=[j]$;
--   3. jumps: unconditional, and conditional on $[i]<0$ as a signed word;
--   4. $\mathtt{read}\ i$: $[i]:=$ the next input word (the all-ones word once the input is exhausted); $\mathtt{write}\ i$: append $[i]$ to the output;
--   5. $\mathtt{halt}$.
--
--   Every executed instruction is one step. The machine is **online**: it sees the input only through reads, one word at a time. The $k$-th read of a run executes at step $t$ when the instruction executed at step $t$ is a read and $k-1$ reads were executed before it; steps between two reads measure the time spent on one input word.
--
--   **Formalization Note** Operands are direct addresses; input words are loaded with `BitVec.ofNat`. A halted machine (at `halt` or outside the program) stays put.
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), §7, p.56 (PDF 58), machine model

import Mathlib

namespace DynSetCover

/-! # The online word-RAM of §7

Paul, Solomon, *Weighted Set Cover with Constant Worst-Case Recourse* (STOC 2027 submission,
sha256 a671756b…), §7, p.56 (PDF 58): "We use a word-RAM with constant-time arithmetic, integer
division, comparisons, bit operations, and table access. A word holds an input address, a signed
cost exponent, or any of the O(log N)-bit integers used below."

**Formalization Note.** A machine with word size `W` has memory `ℕ → BitVec W`, all zero
initially, and a program counter. Operands `i j k` are direct addresses; `load`/`store` are the
indirect accesses ("table access"). Arithmetic is modulo `2^W`; `udiv x 0 = 0` and
`umod x 0 = x` (the `BitVec` conventions). Comparisons are `bltz` (branch if the word is negative
as a signed word, i.e. its top bit is set) together with `sub`. Every executed instruction costs
one step. The machine is **online**: `read i` stores the next input word (the all-ones word once
the input is exhausted) and `write i` appends a word to the output. Input words are natural
numbers loaded with `BitVec.ofNat`. A program halts at `halt` or when the program counter leaves
the program. -/

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
  | halt
  deriving DecidableEq

/-- A program is a finite list of instructions; execution starts at index `0`. -/
abbrev Program := List Instr

/-- A configuration of the machine with word size `W`. `reads` is the number of `read`
instructions executed so far, and `written` the set of memory cells written so far. -/
structure Config (W : ℕ) where
  pc : ℕ
  mem : ℕ → BitVec W
  input : List ℕ
  output : List ℕ
  reads : ℕ
  written : Finset ℕ

namespace Config

variable {W : ℕ}

/-- Write `v` into cell `a` and advance the program counter. -/
def assign (c : Config W) (a : ℕ) (v : BitVec W) : Config W :=
  { c with pc := c.pc + 1, mem := Function.update c.mem a v, written := insert a c.written }

end Config

/-- One step of execution. A halted configuration is left unchanged. -/
def step {W : ℕ} (P : Program) (c : Config W) : Config W :=
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
  | some (Instr.bltz i l) => if (c.mem i).msb then { c with pc := l } else { c with pc := c.pc + 1 }
  | some (Instr.jmp l) => { c with pc := l }
  | some (Instr.read i) =>
      { c.assign i (match c.input with
                    | [] => BitVec.allOnes W
                    | x :: _ => BitVec.ofNat W x) with
        input := c.input.tail, reads := c.reads + 1 }
  | some (Instr.write i) => { c with pc := c.pc + 1, output := c.output ++ [(c.mem i).toNat] }

/-- The initial configuration on input `inp`: program counter `0`, all memory zero. -/
def initConfig (W : ℕ) (inp : List ℕ) : Config W :=
  ⟨0, fun _ => 0, inp, [], 0, ∅⟩

/-- The configuration before step `t` (after `t` steps) of program `P` on input `inp`. -/
def conf (W : ℕ) (P : Program) (inp : List ℕ) (t : ℕ) : Config W :=
  (step (W := W) P)^[t] (initConfig W inp)

/-- `ReadsAt W P inp k t`: the `k`-th `read` instruction of the run (counting from `1`) is the
instruction executed at step `t` (that is, in the configuration reached after `t` steps). -/
def ReadsAt (W : ℕ) (P : Program) (inp : List ℕ) (k t : ℕ) : Prop :=
  (∃ i, P[(conf W P inp t).pc]? = some (Instr.read i)) ∧ (conf W P inp t).reads + 1 = k

/-- The words written strictly between steps `t₁` and `t₂` (`t₁ ≤ t₂`). -/
def outputBetween (W : ℕ) (P : Program) (inp : List ℕ) (t₁ t₂ : ℕ) : List ℕ :=
  (conf W P inp t₂).output.drop (conf W P inp t₁).output.length

end DynSetCover



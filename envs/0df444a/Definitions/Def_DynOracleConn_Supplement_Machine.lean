-- Prove2me | Definitions.Def_DynOracleConn_Supplement_Machine
-- name    : DynOracleConn_Supplement_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:45:35.016249+00:00
-- url     : https://prove2.me/theorems/ec05a1dd-45d1-4df7-8127-a5bfec0b31c3
-- title:
--   A word RAM with adjacency oracle instructions and uniform random words
-- statement:
--   The upper bounds are stated for programs of a **unit-cost word RAM**. A program is a finite list of instructions acting on a memory of words of $w$ bits, $[0],[1],[2],\dots$, all initially $0$. The instructions are the following.
--
--   1. Arithmetic modulo $2^w$, bitwise operations and shifts.
--   2. Indirect load and store, a jump, and a jump if a word is negative as a signed word.
--   3. `coin`, which stores the next independent uniformly random word.
--   4. `read`, which stores the next delivered input word, and `write`, which appends a word to the output.
--   5. The oracle instructions $\mathrm{Adjacent}(u,v)$, $\mathrm{Degree}(v)$ and $\mathrm{Neighbor}(v,j)$, which pass word values to an oracle and store its reply.
--   6. `halt`.
--
--   Every executed instruction is one step, and an oracle instruction also counts as one query. A `read` with no pending input **blocks**: the machine has then finished the current update. The **space** reached by a configuration is one more than the largest address that any executed instruction has read or written. This counts the memory kept between updates and the temporary memory used inside an update alike. The random tape has the law of independent uniform words.
--
--   This is the paper's model (§1.1): "All writable memory counts toward the space bound", "time [is] the number of word operations, including oracle calls", and "A randomized algorithm may additionally read independent, uniformly random words."
--
--   **Formalization Note** The paper fixes no instruction set. The one here is standard; division by $0$ follows the `BitVec` conventions ($x/0=0$, $x \bmod 0=x$). A `halt`, or a program counter outside the program, stops the machine for ever, and then the current update never completes. The time to complete is $\infty$ in that case.
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §1.1, p.4; §2, p.15

import Mathlib

namespace DynOracleConn

/-!
# A word RAM with oracle instructions and uniform random words

Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §1.1, p.4: "The graph is stored
externally and is available only through a read-only oracle; the algorithm has a separate read–write
working memory. All writable memory counts toward the space bound, including both the information
retained between updates and the temporary storage used while processing an update. […] A word
contains Θ(log n) bits." "We measure three quantities of an algorithm: its space, the number S of
words of its working memory; its queries, the number of oracle calls it makes while processing an
update; and its time, the number of word operations, including oracle calls, it performs while
processing an update." "A randomized algorithm may additionally read independent, uniformly random
words." The queries: `Degree(v)`, `Neighbor(v, j)` (list model) and `Adjacent(u, v)` (matrix model).

**Formalization Note.**
1. The paper names a word RAM and no instruction set. A program is a finite list of instructions of a
   unit-cost RAM with words `BitVec w`: arithmetic modulo `2^w` (with the `BitVec` conventions
   `udiv x 0 = 0`, `umod x 0 = x`), bitwise operations, shifts, indirect load and store, a signed
   test-and-jump, a coin instruction that stores the next word of the random tape, `read` of the next
   delivered input word, `write` of an output word, and three oracle instructions. `[i]` is memory
   cell `i`; memory is `ℕ → BitVec w`, initially zero.
2. Oracle instructions pass the word values of their operands to an oracle `O : OCall → ℕ` and
   store the reply (reduced modulo `2^w`); each one is a single step and counts as one query.
3. `read i` stores the next pending input word and **blocks** when none is pending; a configuration
   blocked at a `read` with nothing pending has finished the current update (`IsCompleted`). A
   `halt`, or a program counter outside the program, stops the machine for ever, so that update
   never completes.
4. `top` is `1 +` the largest memory address that any executed instruction has read or written
   (`0` before any access); it never decreases. Space is measured by it: a machine whose `top` is at
   most `S` has only touched cells `0, …, S − 1`.
5. `time P ω O c` is the number of steps from `c` to the first completed configuration, and `⊤` if
   there is none; `complete` returns that configuration.
6. `coinMeasure w` is the law of the random tape: independent uniform words.
-/

namespace Supplement

open MeasureTheory

/-- An oracle call with word-valued arguments: `Adjacent(u, v)`, `Degree(v)` and `Neighbor(v, j)`. -/
inductive OCall : Type where
  | adj (u v : ℕ) : OCall
  | deg (v : ℕ) : OCall
  | nbr (v j : ℕ) : OCall

/-- The instruction set. `[i]` denotes memory cell `i`. -/
inductive Instr : Type where
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
  /-- `[i] :=` the next word of the random tape -/
  | coin (i : ℕ)
  /-- `[i] :=` the next pending input word; blocks if none is pending -/
  | read (i : ℕ)
  /-- append `[i]` to the output -/
  | write (i : ℕ)
  /-- `[i] := Adjacent([j], [k])` -/
  | adj (i j k : ℕ)
  /-- `[i] := Degree([j])` -/
  | deg (i j : ℕ)
  /-- `[i] := Neighbor([j], [k])` -/
  | nbr (i j k : ℕ)
  /-- stop for ever -/
  | halt

/-- A program is a finite list of instructions; execution starts at index `0`. -/
abbrev Program : Type := List Instr

/-- A deterministic program: it contains no coin instruction. -/
def NoCoin (P : Program) : Prop :=
  ∀ i : ℕ, Instr.coin i ∉ P

/-- A configuration of the machine with word size `w`. -/
structure Config (w : ℕ) where
  /-- program counter -/
  pc : ℕ
  /-- memory -/
  mem : ℕ → BitVec w
  /-- the pending input words -/
  input : List ℕ
  /-- the position of the next unused word of the random tape -/
  coinPos : ℕ
  /-- the words written since the current update was delivered -/
  output : List ℕ
  /-- `1 +` the largest memory address accessed so far (`0` if none) -/
  top : ℕ
  /-- the number of oracle calls since the current update was delivered -/
  queries : ℕ

namespace Config

variable {w : ℕ}

/-- Record an access to the cells `as`. -/
def touch (c : Config w) (as : List ℕ) : Config w :=
  { c with top := as.foldl (fun m a => max m (a + 1)) c.top }

/-- Write `v` into cell `a` and advance the program counter (no access is recorded here). -/
def assign (c : Config w) (a : ℕ) (v : BitVec w) : Config w :=
  { c with pc := c.pc + 1, mem := Function.update c.mem a v }

/-- The configuration before the first update: everything zero, the words `inp` pending. -/
def initial (w : ℕ) (inp : List ℕ) : Config w :=
  { pc := 0, mem := fun _ => 0, input := inp, coinPos := 0, output := [], top := 0, queries := 0 }

end Config

/-- One step on random tape `ω` with oracle `O`. A configuration at `halt`, outside the program, or at
a `read` with no pending input is left unchanged. -/
def step {w : ℕ} (P : Program) (ω : ℕ → BitVec w) (O : OCall → ℕ) (c : Config w) : Config w :=
  match P[c.pc]? with
  | none => c
  | some Instr.halt => c
  | some (Instr.one i) => (c.touch [i]).assign i 1
  | some (Instr.add i j k) => (c.touch [i, j, k]).assign i (c.mem j + c.mem k)
  | some (Instr.sub i j k) => (c.touch [i, j, k]).assign i (c.mem j - c.mem k)
  | some (Instr.mul i j k) => (c.touch [i, j, k]).assign i (c.mem j * c.mem k)
  | some (Instr.udiv i j k) => (c.touch [i, j, k]).assign i (BitVec.udiv (c.mem j) (c.mem k))
  | some (Instr.umod i j k) => (c.touch [i, j, k]).assign i (BitVec.umod (c.mem j) (c.mem k))
  | some (Instr.band i j k) => (c.touch [i, j, k]).assign i (c.mem j &&& c.mem k)
  | some (Instr.bor i j k) => (c.touch [i, j, k]).assign i (c.mem j ||| c.mem k)
  | some (Instr.bxor i j k) => (c.touch [i, j, k]).assign i (c.mem j ^^^ c.mem k)
  | some (Instr.shl i j k) => (c.touch [i, j, k]).assign i (c.mem j <<< (c.mem k).toNat)
  | some (Instr.shr i j k) => (c.touch [i, j, k]).assign i (c.mem j >>> (c.mem k).toNat)
  | some (Instr.load i j) =>
      (c.touch [i, j, (c.mem j).toNat]).assign i (c.mem (c.mem j).toNat)
  | some (Instr.store i j) =>
      (c.touch [i, j, (c.mem i).toNat]).assign (c.mem i).toNat (c.mem j)
  | some (Instr.bltz i l) =>
      if (c.mem i).msb then { c.touch [i] with pc := l } else { c.touch [i] with pc := c.pc + 1 }
  | some (Instr.jmp l) => { c with pc := l }
  | some (Instr.coin i) =>
      { (c.touch [i]).assign i (ω c.coinPos) with coinPos := c.coinPos + 1 }
  | some (Instr.read i) =>
      match c.input with
      | [] => c
      | x :: rest => { (c.touch [i]).assign i (BitVec.ofNat w x) with input := rest }
  | some (Instr.write i) =>
      { c.touch [i] with pc := c.pc + 1, output := c.output ++ [(c.mem i).toNat] }
  | some (Instr.adj i j k) =>
      { (c.touch [i, j, k]).assign i
          (BitVec.ofNat w (O (OCall.adj (c.mem j).toNat (c.mem k).toNat))) with
        queries := c.queries + 1 }
  | some (Instr.deg i j) =>
      { (c.touch [i, j]).assign i (BitVec.ofNat w (O (OCall.deg (c.mem j).toNat))) with
        queries := c.queries + 1 }
  | some (Instr.nbr i j k) =>
      { (c.touch [i, j, k]).assign i
          (BitVec.ofNat w (O (OCall.nbr (c.mem j).toNat (c.mem k).toNat))) with
        queries := c.queries + 1 }

/-- The configuration after `t` steps from `c`. -/
def run {w : ℕ} (P : Program) (ω : ℕ → BitVec w) (O : OCall → ℕ) (c : Config w) (t : ℕ) :
    Config w :=
  (step P ω O)^[t] c

/-- A **completed** configuration: blocked at a `read` with no input pending. -/
def IsCompleted {w : ℕ} (P : Program) (c : Config w) : Prop :=
  (∃ i, P[c.pc]? = some (Instr.read i)) ∧ c.input = []

/-- The number of steps from `c` to the first completed configuration, and `⊤` if no completed
configuration is ever reached. -/
noncomputable def time {w : ℕ} (P : Program) (ω : ℕ → BitVec w) (O : OCall → ℕ) (c : Config w) :
    ℕ∞ :=
  ⨅ (t : ℕ) (_ : IsCompleted P (run P ω O c t)), (t : ℕ∞)

open Classical in
/-- The first completed configuration reached from `c`, if there is one. -/
noncomputable def complete {w : ℕ} (P : Program) (ω : ℕ → BitVec w) (O : OCall → ℕ)
    (c : Config w) : Option (Config w) :=
  if h : ∃ t, IsCompleted P (run P ω O c t) then some (run P ω O c (Nat.find h)) else none

/-- The discrete σ-algebra on words. -/
instance (w : ℕ) : MeasurableSpace (BitVec w) := ⊤

/-- The law of the random tape: independent uniformly random words. -/
noncomputable def coinMeasure (w : ℕ) : Measure (ℕ → BitVec w) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (BitVec w)).toMeasure

end Supplement

end DynOracleConn



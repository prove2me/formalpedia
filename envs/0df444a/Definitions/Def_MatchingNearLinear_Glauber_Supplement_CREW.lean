-- Prove2me | Definitions.Def_MatchingNearLinear_Glauber_Supplement_CREW
-- name    : MatchingNearLinear_Glauber_Supplement_CREW
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:52:41.182692+00:00
-- url     : https://prove2.me/theorems/ef8d252a-7c2b-49c6-8b11-619268e0eaf6
-- title:
--   A randomized CREW PRAM with a closed instruction set
-- statement:
--   The computational model of §2.3 for the parallel and sequential algorithms of this paper, made operational. A **program** is a register count and a finite list of instructions; it does not depend on the input. Each processor has real registers and natural-number word registers. The instructions are: constants; copies; exact real arithmetic $+,-,\times,\div$ (division by zero faults); word arithmetic (add, truncated subtract, multiply, div, mod, bitwise and/or/xor, shifts, comparisons); real comparison $\le$; conversion of a word to a real; indirect loads and stores of real and word cells; the processor's own index; an **exact uniform choice** from $\{0,\dots,k-1\}$ for a word $k\ge1$; a **Bernoulli draw** $\mathrm{Ber}(p)$ for a real register $p\in[0,1]$; conditional branch and jump; activation (spawn) of an idle processor at an entry point; writing a real or a word to an output cell; and halt. There is no sorting, reduction, sampling-from-a-law or other aggregate instruction.
--
--   Execution is synchronous. In each step every active processor executes one instruction against the memory of the previous step. Concurrent reads are allowed. Two processors storing to the same memory cell, or emitting to the same output cell, in one step make the run invalid (**exclusive write**); so do faulting instructions, a spawn of a busy processor, and any word value, word cell, address or processor index reaching the **capacity** $(s+2)^{r+1}$, where $s$ is a size parameter of the input and $r$ a fixed exponent (words of $\Theta(\log s)$ bits).
--
--   The randomness of a run is a family $\omega=(U_{t,i})$ of independent uniform variables on $[0,1]$, one per step $t$ and processor $i$, with the product law. A uniform choice from $\{0,\dots,k-1\}$ returns $\min(\lfloor kU\rfloor,k-1)$ and a Bernoulli draw returns $1$ iff $U<p$, so they have exactly the uniform and $\mathrm{Ber}(p)$ laws. A run **halts at time $t$** when after exactly $t$ steps no processor is active for the first time; $t$ is its **depth** and the accumulated number of executed instructions is its **work**. The probability of a property of the halted run is the product measure of the set of $\omega$ whose run halts with that property. A program is **deterministic** if it has no random instruction and **sequential** if it has no spawn instruction (the single-processor random-choice RAM).
--
--   **Formalization Note** The probability of an event is the measure of the set of randomness sequences, i.e. the push-forward of the product law through execution. A synchronous PRAM's step count equals its dependency depth.
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), §2.3, printed p. 9 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib

set_option autoImplicit false

/-!
# A randomized CREW PRAM with a closed instruction set

Miao–Yin, *Sampling Matchings in Near-linear Time*, STOC 2027 submission #444, §2.3
(printed p. 9, PDF p. 11): unit cost for arithmetic operations, comparisons, exact uniform
choices and Bernoulli draws; parallel computation on a CREW PRAM, with work the total number of
operations and depth the number of synchronous steps. Programs are finite instruction lists;
there are no aggregate, sorting or oracle instructions, word values and addresses stay below a
polynomial capacity, and two simultaneous writes to one cell make the run invalid (exclusive write).
The randomness of a run is a family of independent uniform variables, one per (step, processor);
the outcome law of a program is the push-forward of their product measure through execution.
-/

namespace MatchingNearLinear.Glauber.Supplement.CREW

open MeasureTheory
open scoped unitInterval

noncomputable section

/-- A memory or output cell: blank, an exact real, or a natural-number word. -/
inductive Cell where
  | blank
  | num (x : ℝ)
  | word (x : ℕ)
  deriving Inhabited

inductive NumOp where
  | add | sub | mul | div
  deriving DecidableEq

inductive WordOp where
  | add | sub | mul | div | mod | band | bor | xor | shl | shr | lt | eq
  deriving DecidableEq

/-- The instruction set. `uniform d k` writes an exact uniform choice from `{0,…,k-1}` (for a
word `k ≥ 1`); `bernoulli d p` writes a `Ber(p)` draw (for a real `p ∈ [0,1]`). -/
inductive Instruction (registers : ℕ) where
  | constantNum (dst : Fin registers) (x : ℚ)
  | constantWord (dst : Fin registers) (x : ℕ)
  | copyNum (dst src : Fin registers)
  | copyWord (dst src : Fin registers)
  | arithmeticNum (op : NumOp) (dst a b : Fin registers)
  | arithmeticWord (op : WordOp) (dst a b : Fin registers)
  | compareNum (dst a b : Fin registers)
  | wordToNum (dst src : Fin registers)
  | loadNum (dst address : Fin registers)
  | loadWord (dst address : Fin registers)
  | storeNum (address src : Fin registers)
  | storeWord (address src : Fin registers)
  | processorId (dst : Fin registers)
  | uniform (dst bound : Fin registers)
  | bernoulli (dst prob : Fin registers)
  | branchZero (src : Fin registers) (ifZero ifNonzero : ℕ)
  | jump (target : ℕ)
  | spawn (processor : Fin registers) (entry : ℕ)
  | outputNum (address src : Fin registers)
  | outputWord (address src : Fin registers)
  | halt

/-- A program: a register count and a finite list of instructions. -/
structure Program where
  registers : ℕ
  code : List (Instruction registers)

/-- A program that draws no random choice. -/
def Program.Deterministic (P : Program) : Prop :=
  ∀ ins ∈ P.code, (∀ d b, ins ≠ .uniform d b) ∧ (∀ d b, ins ≠ .bernoulli d b)

/-- A program that never activates a second processor (a sequential random-choice RAM). -/
def Program.Sequential (P : Program) : Prop :=
  ∀ ins ∈ P.code, ∀ a e, ins ≠ .spawn a e

structure Thread (registers : ℕ) where
  pc : Option ℕ
  num : Fin registers → ℝ
  word : Fin registers → ℕ

def idle (R : ℕ) : Thread R := ⟨none, fun _ => 0, fun _ => 0⟩
def start (R entry : ℕ) : Thread R := ⟨some entry, fun _ => 0, fun _ => 0⟩

structure Configuration (R : ℕ) where
  thread : ℕ → Thread R
  memory : ℕ → Cell
  result : ℕ → Cell
  work : ℕ

structure Effect (R : ℕ) where
  next : Thread R
  store : Option (ℕ × Cell) := none
  emit : Option (ℕ × Cell) := none
  fork : Option (ℕ × ℕ) := none
  addresses : List ℕ := []

def nextPC {R : ℕ} (t : Thread R) (p : ℕ) : Thread R := {t with pc := some (p + 1)}
def putNum {R : ℕ} (t : Thread R) (d : Fin R) (x : ℝ) : Thread R :=
  {t with num := Function.update t.num d x}
def putWord {R : ℕ} (t : Thread R) (d : Fin R) (x : ℕ) : Thread R :=
  {t with word := Function.update t.word d x}

def NumOp.eval : NumOp → ℝ → ℝ → ℝ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b

def WordOp.eval : WordOp → ℕ → ℕ → ℕ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .band, a, b => Nat.land a b
  | .bor, a, b => Nat.lor a b
  | .xor, a, b => Nat.xor a b
  | .shl, a, b => Nat.shiftLeft a b
  | .shr, a, b => Nat.shiftRight a b
  | .lt, a, b => if a < b then 1 else 0
  | .eq, a, b => if a = b then 1 else 0

/-- Exact uniform choice from `{0,…,k-1}` driven by a uniform `U ∈ [0,1]`
(`⌊kU⌋`, with the null event `U = 1` sent to `k-1`). -/
def uniformChoice (k : ℕ) (U : I) : ℕ := min (⌊(k : ℝ) * (U : ℝ)⌋₊) (k - 1)

/-- A `Ber(p)` draw driven by a uniform `U ∈ [0,1]`: `1` iff `U < p`. -/
def bernoulliDraw (p : ℝ) (U : I) : ℕ := if (U : ℝ) < p then 1 else 0

/-- One active processor executes one primitive with fresh randomness `U`.
Invalid loads, zero divisors, `k = 0` and `p ∉ [0,1]` fault. -/
def effect (P : Program) (pid : ℕ) (U : I) (t : Thread P.registers) (mem : ℕ → Cell) :
    Option (Effect P.registers) := by
  classical
  exact match t.pc with
  | none => some ⟨t, none, none, none, []⟩
  | some pc => do
    let ins ← P.code[pc]?
    let nt := nextPC t pc
    match ins with
    | .constantNum d x => pure ⟨putNum nt d x, none, none, none, []⟩
    | .constantWord d x => pure ⟨putWord nt d x, none, none, none, []⟩
    | .copyNum d a => pure ⟨putNum nt d (t.num a), none, none, none, []⟩
    | .copyWord d a => pure ⟨putWord nt d (t.word a), none, none, none, []⟩
    | .arithmeticNum op d a b =>
      if op = .div ∧ t.num b = 0 then none
      else pure ⟨putNum nt d (op.eval (t.num a) (t.num b)), none, none, none, []⟩
    | .arithmeticWord op d a b =>
      if (op = .div ∨ op = .mod) ∧ t.word b = 0 then none
      else pure ⟨putWord nt d (op.eval (t.word a) (t.word b)), none, none, none, []⟩
    | .compareNum d a b =>
      pure ⟨putWord nt d (if t.num a ≤ t.num b then 1 else 0), none, none, none, []⟩
    | .wordToNum d a => pure ⟨putNum nt d (t.word a), none, none, none, []⟩
    | .loadNum d a => match mem (t.word a) with
      | .num x => pure ⟨putNum nt d x, none, none, none, [t.word a]⟩
      | _ => none
    | .loadWord d a => match mem (t.word a) with
      | .word x => pure ⟨putWord nt d x, none, none, none, [t.word a]⟩
      | _ => none
    | .storeNum a b => pure ⟨nt, some (t.word a, .num (t.num b)), none, none, [t.word a]⟩
    | .storeWord a b => pure ⟨nt, some (t.word a, .word (t.word b)), none, none, [t.word a]⟩
    | .processorId d => pure ⟨putWord nt d pid, none, none, none, []⟩
    | .uniform d b =>
      if t.word b = 0 then none
      else pure ⟨putWord nt d (uniformChoice (t.word b) U), none, none, none, []⟩
    | .bernoulli d b =>
      if 0 ≤ t.num b ∧ t.num b ≤ 1 then
        pure ⟨putWord nt d (bernoulliDraw (t.num b) U), none, none, none, []⟩
      else none
    | .branchZero a z nz =>
      pure ⟨{t with pc := some (if t.word a = 0 then z else nz)}, none, none, none, []⟩
    | .jump target => pure ⟨{t with pc := some target}, none, none, none, []⟩
    | .spawn a entry => pure ⟨nt, none, none, some (t.word a, entry), [t.word a]⟩
    | .outputNum a b => pure ⟨nt, none, some (t.word a, .num (t.num b)), none, [t.word a]⟩
    | .outputWord a b => pure ⟨nt, none, some (t.word a, .word (t.word b)), none, [t.word a]⟩
    | .halt => pure ⟨{t with pc := none}, none, none, none, []⟩

/-- Word capacity `(s+2)^(r+1)` for a size parameter `s`: Θ(log s)-bit words for fixed `r`. -/
def capacity (s r : ℕ) : ℕ := (s + 2) ^ (r + 1)

def initial (P : Program) (input : List Cell) : Configuration P.registers :=
  ⟨fun pid => if pid = 0 then start P.registers 0 else idle P.registers,
    fun a => input[a]?.getD .blank, fun _ => .blank, 0⟩

def active {R : ℕ} (cap : ℕ) (c : Configuration R) : Finset ℕ :=
  (Finset.range cap).filter (fun pid => (c.thread pid).pc.isSome)

def Halted {R : ℕ} (cap : ℕ) (c : Configuration R) : Prop := active cap c = ∅

/-- Every word value, word cell and address in use is below the capacity. -/
def Bounded {R : ℕ} (cap : ℕ) (c : Configuration R) : Prop :=
  (∀ pid < cap, ∀ j, (c.thread pid).word j < cap) ∧
  (∀ a z, c.memory a = .word z → a < cap ∧ z < cap) ∧
  (∀ a x, c.memory a = .num x → a < cap) ∧
  (∀ a z, c.result a = .word z → a < cap ∧ z < cap) ∧
  (∀ a x, c.result a = .num x → a < cap)

/-- Randomness of a run: one independent uniform variable per (step, processor). -/
abbrev Randomness := ℕ × ℕ → I

/-- The product of the uniform laws on `[0,1]`. -/
def randomnessLaw : Measure Randomness := Measure.infinitePi (fun _ : ℕ × ℕ => volume)

/-- Synchronous CREW step at time `time`; reads see the old memory. Concurrent reads are allowed;
two processors storing to one memory cell, or emitting to one output cell, in the same step
make the step invalid (exclusive write). A fork activates one idle processor. -/
def step (P : Program) (cap time : ℕ) (ω : Randomness)
    (c : Configuration P.registers) : Option (Configuration P.registers) := by
  classical
  let es := fun pid => effect P pid (ω (time, pid)) (c.thread pid) c.memory
  let get := fun pid => (es pid).getD ⟨idle P.registers, none, none, none, []⟩
  let forks := fun target => (Finset.range cap).filter
    (fun pid => ∃ entry, (get pid).fork = some (target, entry))
  let memWriters := fun a => (Finset.range cap).filter
    (fun pid => ∃ x, (get pid).store = some (a, x))
  let outWriters := fun a => (Finset.range cap).filter
    (fun pid => ∃ x, (get pid).emit = some (a, x))
  let ready : Prop := Bounded cap c ∧
    (∀ pid < cap, (es pid).isSome = true) ∧
    (∀ pid < cap, ∀ a ∈ (get pid).addresses, a < cap) ∧
    (∀ pid < cap, ∀ target entry, (get pid).fork = some (target, entry) →
      target < cap ∧ (c.thread target).pc = none ∧ entry < P.code.length ∧
        ∀ other ∈ forks target, other = pid) ∧
    (∀ a, (memWriters a).card ≤ 1) ∧ (∀ a, (outWriters a).card ≤ 1)
  let after : Configuration P.registers :=
    ⟨fun pid => if pid < cap then
        if h : (forks pid).Nonempty then
          let parent := (forks pid).min' h
          start P.registers (((get parent).fork).getD (0, 0)).2
        else (get pid).next
      else idle P.registers,
     fun a => if h : (memWriters a).Nonempty then
        (((get ((memWriters a).min' h)).store).getD (a, .blank)).2
      else c.memory a,
     fun a => if h : (outWriters a).Nonempty then
        (((get ((outWriters a).min' h)).emit).getD (a, .blank)).2
      else c.result a,
     c.work + (active cap c).card⟩
  exact if ready ∧ Bounded cap after then some after else none

/-- The configuration after `t` synchronous steps; `none` once the run has faulted. -/
def run (P : Program) (cap : ℕ) (input : List Cell) (ω : Randomness) :
    ℕ → Option (Configuration P.registers)
  | 0 => some (initial P input)
  | t + 1 => do
    let c ← run P cap input ω t
    step P cap t ω c

/-- The run on randomness `ω` first halts after exactly `t` steps, in configuration `c`
(so its depth is `t`, its work is `c.work` and its outputs are `c.result`). -/
def HaltsAt (P : Program) (cap : ℕ) (input : List Cell) (ω : Randomness) (t : ℕ)
    (c : Configuration P.registers) : Prop :=
  run P cap input ω t = some c ∧ Halted cap c ∧
    ∀ t' < t, ∀ c', run P cap input ω t' = some c' → ¬ Halted cap c'

/-- The run on `ω` halts without fault. -/
def Halts (P : Program) (cap : ℕ) (input : List Cell) (ω : Randomness) : Prop :=
  ∃ t c, HaltsAt P cap input ω t c

/-- Probability, under `randomnessLaw`, of a property of the halted run. -/
def prob (P : Program) (cap : ℕ) (input : List Cell)
    (E : ℕ → Configuration P.registers → Prop) : ℝ :=
  (randomnessLaw {ω | ∃ t c, HaltsAt P cap input ω t c ∧ E t c}).toReal

end

end MatchingNearLinear.Glauber.Supplement.CREW



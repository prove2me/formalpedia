-- Prove2me | Definitions.Def_PatternRangeCounting1593_RangeCounting_Machine
-- name    : PatternRangeCounting1593_RangeCounting_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:02.443534+00:00
-- url     : https://prove2.me/theorems/0545dbcf-3bc9-423b-876c-b2eb0ba723a6
-- title:
--   The deterministic word RAM of §3.1: instructions, runs, packed bit buffers, queries and constructions
-- statement:
--   The model of computation is a deterministic word RAM with $w$-bit words. A program is a finite list of instructions over registers $r_0,r_1,\dots$ and a memory $\mathrm{mem}:\mathbb N\to\mathbb N$; every register and memory cell holds an integer in $[0,2^w)$. The instructions are:
--
--   1. load a constant; addition, subtraction and multiplication modulo $2^w$;
--   2. bitwise AND, OR, XOR and complement; shifts $x\cdot 2^y \bmod 2^w$ and $\lfloor x/2^y\rfloor$;
--   3. the index of the most significant set bit of a nonzero word;
--   4. indirect load $r_d:=\mathrm{mem}[r_a]$ and store $\mathrm{mem}[r_a]:=r_s$;
--   5. an unconditional jump, jumps on $r_a<r_b$ and on $r_a=r_b$, and halt.
--
--   Every executed instruction costs one step. There is no division and no instruction evaluating an arbitrary function; fetching outside the program never halts. The **working-word** measure of a run is one more than the largest memory address loaded or stored.
--
--   A bit string $\beta$ of length $B$ is stored **packed**: word $j$ holds bits $jw,\dots,jw+w-1$ of $\beta$, so $\beta$ occupies $\lceil B/w\rceil$ words. A **static query** starts on the packed buffer with its inputs in registers and must halt within a given number of steps with the answers in $r_0,r_1,\dots$; a **read-only** query in addition leaves memory unchanged. A **construction** starts on its input (for a permutation, $\mathrm{mem}[j]=\tau(j+1)$ for $j<n$ and $r_0=n$) and must halt within a given number of steps with a pointer to a packed output buffer in $r_0$, its length in $r_1$, and all touched addresses and the output below a given working-word bound. A component placed inside a larger buffer at bit offset $o$ is said to occur there.
--
--   The admissible word sizes for input size $n$ are $2\,b(N)\le w\le K\,b(N)$, where $N=\max\{2,n\}$, $b(N)$ is its bit length and $K\ge 2$ is a fixed parameter: this is $w=\Theta(\log N)$ with the word long enough for a pair of coordinates. The time unit $\lfloor\log_2\lfloor\log_2 m\rfloor\rfloor+1$ measures $O(\log\log m)$.
--
--   This machine is the one on which every algorithmic statement of the mission is phrased.
--
--   **Formalization Note** One program serves every word size; constants in instructions are read modulo $2^w$.
-- source:
--   Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), §3.1, printed p. 10 (PDF p. 11)

import Mathlib

set_option autoImplicit false

namespace PatternRangeCounting1593.RangeCounting

/-!
# The deterministic word RAM of §3.1

Sankardeep Chakraborty, STOC 2027 submission #1593 (October 2026), §3.1, printed p. 10
(PDF p. 11): "We use a deterministic word RAM with w = Θ(log N)-bit words … Standard word
operations, including multiplication and finding the most significant set bit of a nonzero word,
take constant time. The word length is sufficient to store a pair of coordinates."

A program is a finite list of instructions over registers `r₀, r₁, …` and a memory
`mem : ℕ → ℕ`; every register and memory cell holds a `w`-bit word (an integer in `[0, 2^w)`),
results are reduced modulo `2^w`. There is no division instruction and no instruction evaluating
an arbitrary function. Every executed instruction costs one step. Fetching outside the program
is stuck (the run never halts).
-/

/-- The instruction set. Register indices are natural numbers fixed in the program text. -/
inductive Instr where
  /-- `r_d := v mod 2^w` -/
  | const (d v : ℕ)
  /-- `r_d := (r_a + r_b) mod 2^w` -/
  | add (d a b : ℕ)
  /-- `r_d := (r_a - r_b) mod 2^w` -/
  | sub (d a b : ℕ)
  /-- `r_d := (r_a · r_b) mod 2^w` -/
  | mul (d a b : ℕ)
  /-- bitwise AND -/
  | band (d a b : ℕ)
  /-- bitwise OR -/
  | bor (d a b : ℕ)
  /-- bitwise XOR -/
  | bxor (d a b : ℕ)
  /-- bitwise complement within `w` bits -/
  | bnot (d a : ℕ)
  /-- `r_d := (r_a · 2^{r_b}) mod 2^w` -/
  | shl (d a b : ℕ)
  /-- `r_d := ⌊r_a / 2^{r_b}⌋` -/
  | shr (d a b : ℕ)
  /-- `r_d :=` index of the most significant set bit of `r_a` (`0` when `r_a = 0`) -/
  | msb (d a : ℕ)
  /-- `r_d := mem[r_a]` -/
  | load (d a : ℕ)
  /-- `mem[r_a] := r_s` -/
  | store (a s : ℕ)
  /-- unconditional jump -/
  | jmp (t : ℕ)
  /-- jump to `t` if `r_a < r_b` -/
  | jlt (a b t : ℕ)
  /-- jump to `t` if `r_a = r_b` -/
  | jeq (a b t : ℕ)
  /-- stop -/
  | halt
  deriving DecidableEq, Repr

/-- A program: a finite instruction list; execution starts at index `0`. -/
abbrev Program := List Instr

/-- A machine state. `maxAddr` is one more than the largest memory address loaded or stored so
far (the working-word measure). -/
structure State where
  pc : ℕ
  regs : ℕ → ℕ
  mem : ℕ → ℕ
  halted : Bool
  maxAddr : ℕ

/-- One step at word size `w`. A halted state is fixed; a `pc` outside the program is stuck. -/
def step (w : ℕ) (P : Program) (s : State) : State :=
  if s.halted then s else
  match P[s.pc]? with
  | none => s
  | some i =>
    let M := 2 ^ w
    let r := s.regs
    let set := fun (d v : ℕ) => { s with pc := s.pc + 1, regs := Function.update r d (v % M) }
    match i with
    | .const d v => set d v
    | .add d a b => set d (r a + r b)
    | .sub d a b => set d (r a + M - r b % M)
    | .mul d a b => set d (r a * r b)
    | .band d a b => set d (r a &&& r b)
    | .bor d a b => set d (r a ||| r b)
    | .bxor d a b => set d (r a ^^^ r b)
    | .bnot d a => set d (M - 1 - r a % M)
    | .shl d a b => set d (r a * 2 ^ (r b))
    | .shr d a b => set d (r a / 2 ^ (r b))
    | .msb d a => set d (if r a = 0 then 0 else Nat.log 2 (r a))
    | .load d a =>
        { s with pc := s.pc + 1, regs := Function.update r d (s.mem (r a) % M),
                 maxAddr := max s.maxAddr (r a + 1) }
    | .store a v =>
        { s with pc := s.pc + 1, mem := Function.update s.mem (r a) (r v % M),
                 maxAddr := max s.maxAddr (r a + 1) }
    | .jmp t => { s with pc := t }
    | .jlt a b t => { s with pc := if r a < r b then t else s.pc + 1 }
    | .jeq a b t => { s with pc := if r a = r b then t else s.pc + 1 }
    | .halt => { s with halted := true }

/-- Run for `k` steps. -/
def runN (w : ℕ) (P : Program) : ℕ → State → State
  | 0, s => s
  | k + 1, s => runN w P k (step w P s)

/-- The initial state on memory `mem` with registers `r_j = inputs[j] mod 2^w` (other registers
zero). -/
def initState (w : ℕ) (mem : ℕ → ℕ) (inputs : List ℕ) : State :=
  { pc := 0, regs := fun j => inputs.getD j 0 % 2 ^ w, mem := mem, halted := false, maxAddr := 0 }

/-- Word `j` of the bit string `bits` packed into `w`-bit words: bit `j·w + t` of the string is
bit `t` of the word (missing positions are zero). -/
def packBits (w : ℕ) (bits : List Bool) (j : ℕ) : ℕ :=
  ∑ t ∈ Finset.range w, if bits.getD (j * w + t) false then 2 ^ t else 0

/-- The number of `w`-bit words occupied by `B` packed bits, `⌈B / w⌉`. -/
def numWords (w B : ℕ) : ℕ := (B + w - 1) / w

/-- `X` occurs in `buf` at bit offset `o`. -/
def SliceAt (buf : List Bool) (o : ℕ) (X : List Bool) : Prop :=
  X <+: buf.drop o

/-- A static query: from memory `mem` and register inputs, the run halts within `T` steps with
registers `r₀, r₁, …` holding `outputs`. -/
def RunsQuery (w : ℕ) (P : Program) (mem : ℕ → ℕ) (inputs outputs : List ℕ) (T : ℕ) : Prop :=
  ∃ k ≤ T, (runN w P k (initState w mem inputs)).halted = true ∧
    ∀ j < outputs.length, (runN w P k (initState w mem inputs)).regs j = outputs.getD j 0

/-- A read-only static query: as `RunsQuery`, and the final memory equals the initial memory. -/
def RunsQueryRO (w : ℕ) (P : Program) (mem : ℕ → ℕ) (inputs outputs : List ℕ) (T : ℕ) : Prop :=
  ∃ k ≤ T, (runN w P k (initState w mem inputs)).halted = true ∧
    (∀ j < outputs.length, (runN w P k (initState w mem inputs)).regs j = outputs.getD j 0) ∧
    (runN w P k (initState w mem inputs)).mem = mem

/-- A construction run: from memory `mem` and register inputs, the run halts after at most `time`
steps, its final register `r₀` points to the packed output buffer and `r₁ = |bits|`, the buffer
`mem[r₀ + j] = packBits w bits j` (`j < ⌈|bits|/w⌉`) holds `bits`, registers `r₂, r₃, …` hold
`extra`, and every touched address and the output buffer lie below `words` (peak working words). -/
def BuildsWith (w : ℕ) (P : Program) (mem : ℕ → ℕ) (inputs : List ℕ) (time words : ℝ)
    (bits : List Bool) (extra : List ℕ) : Prop :=
  ∃ k : ℕ, (k : ℝ) ≤ time ∧ (runN w P k (initState w mem inputs)).halted = true ∧
    ((runN w P k (initState w mem inputs)).maxAddr : ℝ) ≤ words ∧
    (((runN w P k (initState w mem inputs)).regs 0 + numWords w bits.length : ℕ) : ℝ) ≤ words ∧
    (runN w P k (initState w mem inputs)).regs 1 = bits.length ∧
    (∀ j < numWords w bits.length,
      (runN w P k (initState w mem inputs)).mem ((runN w P k (initState w mem inputs)).regs 0 + j)
        = packBits w bits j) ∧
    ∀ j < extra.length, (runN w P k (initState w mem inputs)).regs (j + 2) = extra.getD j 0

/-- The constructor input for a permutation: `mem[j] = τ(j+1)` (one-based value) for `j < n`,
zero elsewhere; register `r₀ = n`. -/
def permMem {n : ℕ} (τ : Equiv.Perm (Fin n)) (j : ℕ) : ℕ :=
  if h : j < n then (τ ⟨j, h⟩ : ℕ) + 1 else 0

/-- The admissible word widths for input size `n`: with `N = max{2, n}` and `b(N)` its bit
length, `2·b(N) ≤ w ≤ K·b(N)`. This is `w = Θ(log N)` with explicit constants: the lower bound
stores a pair of coordinates, the parameter `K ≥ 2` is arbitrary. -/
def WidthOK (K n w : ℕ) : Prop :=
  2 * Nat.size (max 2 n) ≤ w ∧ w ≤ K * Nat.size (max 2 n)

/-- `⌊log₂ ⌊log₂ m⌋⌋ + 1`, the `O(log log m)` time unit. -/
def loglogBound (m : ℕ) : ℕ := Nat.log 2 (Nat.log 2 m) + 1

end PatternRangeCounting1593.RangeCounting



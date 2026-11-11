-- Prove2me | Definitions.Def_RobustKZClust_Main_Machine
-- name    : RobustKZClust_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:10:56.72872+00:00
-- url     : https://prove2.me/theorems/e25c42f2-b8fe-4ab0-ad01-ae454073f4a0
-- title:
--   The streaming machine of §2: persistent bit memory, O(1) transient real registers, fair coins, bit space
-- statement:
--   The paper's model (§2): "We allow exact real arithmetic during updates and queries and $O(1)$ real registers; bit-space bounds count stored bit strings and discrete workspace." It names no machine; this definition fixes one.
--
--   A **program** is a finite list of instructions acting on a configuration made of a program counter, an **integer memory** $\mathrm{mem}:\mathbb N\to\mathbb Z$, **real registers** $\mathrm{reg}:\mathbb N\to\mathbb R$, and a count of coins used. The instructions are:
--
--   1. integer operations: constant, $+$, $-$, $\times$, Euclidean quotient and remainder, indirect read and write, unconditional jump, jump if a cell is positive;
--   2. a **fair coin**: write the next bit of the call's random tape into a cell;
--   3. read-only input: copy an integer input word, or a real input number, selected by a cell's value;
--   4. transfers: integer to real, and $\lfloor\cdot\rfloor$ of a real into a cell;
--   5. exact real arithmetic $+,-,\times,\div$ (with $a/0=0$), $\sqrt{\cdot}$ (with $\sqrt{a}=0$ for $a<0$), and jump if a real register is positive.
--
--   A **call** runs a program from location $0$ on a given memory, with every real register $0$, its own random tape and its read-only input, until the program counter leaves the program. The memory is what persists from one call to the next; the real registers do not. A program **uses at most $K$ real registers** if every register index it mentions is below $K$; it is **deterministic** if it has no coin instruction.
--
--   The **space** of a memory is measured in bits: $\mathrm{SpaceLE}(m,B)$ says that the nonzero cells of $m$ have total bit length at most $B$, counting for each nonzero cell the bits of its address and of its content (binary digits plus a sign bit).
--
--   The coins of a whole run are independent fair random tapes, one per call, with the product law $\mathbb P$.
--
--   This is the model in which the mission's space bounds are stated: only integers are stored, real arithmetic is free but transient.
--
--   **Formalization Note.** The space pattern (`SpaceLE`, address charging) follows the published definition `RobustCorrClust_Main_StreamingRAM`, copied here, not imported, because that machine has no real registers and another call interface. Real registers reset at every call: a persistent real register would hold the entire frequency vector in one number and make any space bound trivial. The tape laws are `Measure.infinitePi` of fair bits.
-- source:
--   Guo, Jiang, Krauthgamer, Xie, Zhou, Adversarially Robust Streaming Algorithms for (k, z)-Clustering, STOC 2027 submission (manuscript sha256 7d9aadba…), p. 13, §2 (model paragraph); reading of the mission

import Mathlib

namespace RobustKZClust.Main

/-! The machine reading of §2 (p. 13): "We allow exact real arithmetic during updates and queries
and O(1) real registers; bit-space bounds count stored bit strings and discrete workspace."

A program runs on a memory of integer cells `mem : ℕ → ℤ` (persistent between calls, charged in
bits, addresses included, following the published `RobustCorrClust_Main_StreamingRAM.SpaceLE`
pattern) and on real registers `reg : ℕ → ℝ`, which every call starts at `0` and which do not
survive the call. A call reads its input (a list of integers and a list of reals) read-only. -/

/-- Instructions. `d a b c s` are integer cell addresses, `r p q` real register indices, `t` a
program location. -/
inductive Instr where
  /-- `mem[d] := v` -/
  | const (d : ℕ) (v : ℤ)
  /-- `mem[d] := mem[a] + mem[b]` -/
  | add (d a b : ℕ)
  /-- `mem[d] := mem[a] - mem[b]` -/
  | sub (d a b : ℕ)
  /-- `mem[d] := mem[a] * mem[b]` -/
  | mul (d a b : ℕ)
  /-- `mem[d] := mem[a] / mem[b]` (Euclidean quotient, `0` when `mem[b] = 0`) -/
  | div (d a b : ℕ)
  /-- `mem[d] := mem[a] % mem[b]` (Euclidean remainder) -/
  | mod (d a b : ℕ)
  /-- `mem[d] := mem[|mem[a]|]` (indirect read) -/
  | load (d a : ℕ)
  /-- `mem[|mem[a]|] := mem[s]` (indirect write) -/
  | store (a s : ℕ)
  /-- go to location `t` -/
  | jump (t : ℕ)
  /-- go to location `t` if `mem[c] > 0` -/
  | jumpPos (c t : ℕ)
  /-- `mem[d] :=` the next bit (`0` or `1`) of the call's random tape -/
  | rand (d : ℕ)
  /-- `mem[d] :=` integer input word number `|mem[a]|` (`0` when out of range) -/
  | input (d a : ℕ)
  /-- `reg[r] :=` real input number `|mem[a]|` (`0` when out of range) -/
  | rinput (r a : ℕ)
  /-- `reg[r] := mem[a]` (integer to real) -/
  | ofInt (r a : ℕ)
  /-- `mem[d] := ⌊reg[r]⌋` (real to integer) -/
  | floor (d r : ℕ)
  /-- `reg[r] := reg[p] + reg[q]` -/
  | radd (r p q : ℕ)
  /-- `reg[r] := reg[p] - reg[q]` -/
  | rsub (r p q : ℕ)
  /-- `reg[r] := reg[p] * reg[q]` -/
  | rmul (r p q : ℕ)
  /-- `reg[r] := reg[p] / reg[q]` (`0` when `reg[q] = 0`) -/
  | rdiv (r p q : ℕ)
  /-- `reg[r] := √(reg[p])` (`0` for a negative argument) -/
  | rsqrt (r p : ℕ)
  /-- go to location `t` if `reg[p] > 0` -/
  | rjumpPos (p t : ℕ)

/-- A program: a finite instruction list. -/
abbrev Program := List Instr

/-- The real register indices an instruction mentions. -/
def Instr.regs : Instr → List ℕ
  | .rinput r _ => [r]
  | .ofInt r _ => [r]
  | .floor _ r => [r]
  | .radd r p q => [r, p, q]
  | .rsub r p q => [r, p, q]
  | .rmul r p q => [r, p, q]
  | .rdiv r p q => [r, p, q]
  | .rsqrt r p => [r, p]
  | .rjumpPos p _ => [p]
  | _ => []

/-- The program uses only the real registers `0, …, K − 1`, i.e. at most `K` real registers. -/
def RegsBelow (P : Program) (K : ℕ) : Prop :=
  ∀ i ∈ P, ∀ r ∈ i.regs, r < K

/-- The program never tosses a coin. -/
def Deterministic (P : Program) : Prop :=
  ∀ d, Instr.rand d ∉ P

/-- The read-only input of a call: integer words and real numbers. -/
structure CallInput where
  ints : List ℤ
  reals : List ℝ

/-- A configuration: program counter, integer memory, real registers, coins used. -/
structure Config where
  pc : ℕ
  mem : ℕ → ℤ
  reg : ℕ → ℝ
  coins : ℕ

/-- Next instruction, writing `v` to cell `d`. -/
def Config.write (c : Config) (d : ℕ) (v : ℤ) : Config :=
  { c with pc := c.pc + 1, mem := Function.update c.mem d v }

/-- Next instruction, writing `v` to real register `r`. -/
def Config.rwrite (c : Config) (r : ℕ) (v : ℝ) : Config :=
  { c with pc := c.pc + 1, reg := Function.update c.reg r v }

/-- Execute one instruction with random tape `ω` and call input `inp`. -/
noncomputable def exec (i : Instr) (ω : ℕ → Bool) (inp : CallInput) (c : Config) : Config :=
  match i with
  | .const d v => c.write d v
  | .add d a b => c.write d (c.mem a + c.mem b)
  | .sub d a b => c.write d (c.mem a - c.mem b)
  | .mul d a b => c.write d (c.mem a * c.mem b)
  | .div d a b => c.write d (c.mem a / c.mem b)
  | .mod d a b => c.write d (c.mem a % c.mem b)
  | .load d a => c.write d (c.mem (c.mem a).natAbs)
  | .store a s => c.write (c.mem a).natAbs (c.mem s)
  | .jump t => { c with pc := t }
  | .jumpPos b t => { c with pc := if 0 < c.mem b then t else c.pc + 1 }
  | .rand d => { c.write d (if ω c.coins then 1 else 0) with coins := c.coins + 1 }
  | .input d a => c.write d (inp.ints.getD (c.mem a).natAbs 0)
  | .rinput r a => c.rwrite r (inp.reals.getD (c.mem a).natAbs 0)
  | .ofInt r a => c.rwrite r (c.mem a : ℝ)
  | .floor d r => c.write d ⌊c.reg r⌋
  | .radd r p q => c.rwrite r (c.reg p + c.reg q)
  | .rsub r p q => c.rwrite r (c.reg p - c.reg q)
  | .rmul r p q => c.rwrite r (c.reg p * c.reg q)
  | .rdiv r p q => c.rwrite r (c.reg p / c.reg q)
  | .rsqrt r p => c.rwrite r (Real.sqrt (c.reg p))
  | .rjumpPos p t => { c with pc := if 0 < c.reg p then t else c.pc + 1 }

/-- One step; a configuration past the end of the program is halted and does not change. -/
noncomputable def step (P : Program) (ω : ℕ → Bool) (inp : CallInput) (c : Config) : Config :=
  match P[c.pc]? with
  | some i => exec i ω inp c
  | none => c

/-- The machine has halted. -/
def Halted (P : Program) (c : Config) : Prop := P.length ≤ c.pc

/-- The configuration after `t` steps of a call of `P` on input `inp`, started at location `0`
on the memory `m`, with all real registers `0`, no coins used, and random tape `ω`. -/
noncomputable def callRun (P : Program) (ω : ℕ → Bool) (inp : CallInput) (m : ℕ → ℤ)
    (t : ℕ) : Config :=
  (step P ω inp)^[t] ⟨0, m, fun _ => 0, 0⟩

/-- The configuration in which the call halts (the first halted one); the start configuration
if the call never halts (excluded by the halting clauses of every statement). -/
noncomputable def callFinal (P : Program) (ω : ℕ → Bool) (inp : CallInput) (m : ℕ → ℤ) :
    Config := by
  classical
  exact if h : ∃ t, Halted P (callRun P ω inp m t) then callRun P ω inp m (Nat.find h)
    else ⟨0, m, fun _ => 0, 0⟩

/-- Bit length of an integer word: binary digits of `|v|` plus a sign bit (`wordLen 0 = 1`). -/
def wordLen (v : ℤ) : ℕ := Nat.size v.natAbs + 1

/-- Bit length of an address. -/
def adrLen (a : ℕ) : ℕ := wordLen (a : ℤ)

/-- Space in bits: every finite set of nonzero cells has total address-plus-content bit length at
most `B` (so finitely many cells are nonzero and they occupy at most `B` bits). -/
def SpaceLE (m : ℕ → ℤ) (B : ℝ) : Prop :=
  ∀ S : Finset ℕ, (∀ a ∈ S, m a ≠ 0) → ((∑ a ∈ S, (adrLen a + wordLen (m a)) : ℕ) : ℝ) ≤ B

/-- The memory in which nothing has been stored. -/
def zeroMem : ℕ → ℤ := fun _ => 0

/-- The tape a deterministic call is run on (it never reads it). -/
def blankTape : ℕ → Bool := fun _ => false

/-- The law of one fair bit. -/
noncomputable def coinMeasure : MeasureTheory.Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

instance : MeasureTheory.IsProbabilityMeasure coinMeasure := by
  unfold coinMeasure; infer_instance

/-- The law of one random tape: independent fair bits. -/
noncomputable def tapeMeasure : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi fun _ => coinMeasure

instance : MeasureTheory.IsProbabilityMeasure tapeMeasure := by
  unfold tapeMeasure; infer_instance

/-- The law of the algorithm's coins over a whole run: call number `i` reads its own tape
`ω i`, and the tapes are independent. -/
noncomputable def tapesMeasure : MeasureTheory.Measure (ℕ → ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi fun _ => tapeMeasure

instance : MeasureTheory.IsProbabilityMeasure tapesMeasure := by
  unfold tapesMeasure; infer_instance

end RobustKZClust.Main



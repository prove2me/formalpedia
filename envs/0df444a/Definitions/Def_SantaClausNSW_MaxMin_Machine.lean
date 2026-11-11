-- Prove2me | Definitions.Def_SantaClausNSW_MaxMin_Machine
-- name    : SantaClausNSW_MaxMin_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:34:07.381888+00:00
-- url     : https://prove2.me/theorems/8b5ff718-33be-464d-b375-e2daa64b7c05
-- title:
--   A randomized RAM over exact rationals with fair coins, an exact rational sampler, an oracle port and bit-cost work
-- statement:
--   The paper names no machine model. A **program** is a finite list of instructions acting on a memory of rational cells indexed by the integers: constant, addition, subtraction, multiplication, division (with $q/0=0$), floor, indirect load and store, a jump taken when $[i]<[j]$, a **fair coin** writing $0$ or $1$ with probability $1/2$ each, an **exact sampling** instruction that reads a list $q_0,\dots,q_{k-1}$ from memory and, if it is a probability distribution, writes $t$ with probability $q_t$ (otherwise $-1$), an **oracle call** that sends a list of rationals to the oracle (a fixed function from lists to lists) and writes the answer back, and halt.
--
--   Every step costs $1$ plus the bit lengths of the addresses, operands, results, sampled lists, oracle questions and answers it touches; the semantics is a probability distribution over machine states, with halted states absorbing. The input is placed in cells $0,1,2,\dots$; the output list is read after halting from cells $-2,-3,\dots$, with its length in cell $-1$.
--
--   A program **halts within $B$** on an input if every run, for every outcome of its coins and samples, has halted with work at most $B$. A program is **coin-only** if it contains no sampling instruction. `outProb` is the probability that the output list satisfies an event, `condProbOf` a conditional probability $\Pr[E\mid F]=\Pr[E\wedge F]/\Pr[F]$.
--
--   For Appendix E.2 the module also defines **capped rejection sampling**: a sampling call on a distribution with common denominator $Q$ draws $\lceil\log_2Q\rceil$ fair bits, accepts the integer if it is below $Q$ and maps it to an outcome by the prescribed probabilities, repeats at most $T$ times and aborts the run if no trial is accepted; `runCapped` runs a program with every sampling call executed this way.
--
--   **Formalization Note.** The memory is `ℤ → ℚ`; the run law after $k$ steps is a `PMF State`. Since every step costs at least $1$, a run with work at most $B$ has halted after $B+1$ steps, so `HaltsWithin` and `outProb` look at the law after $B+1$ steps.
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 10 §2 (oracles, running time); p. 33 (fair coins); p. 67 App. E.1–E.2

import Mathlib

namespace SantaClausNSW.MaxMin

/-!
# A randomized oracle RAM over exact rationals

Chen, Feng, Hu, Li, Zhang, *Santa Claus and Weighted Nash Social Welfare with Subadditive
Valuations*, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 10 §2 (oracles and
running-time convention), p. 67 App. E.1–E.2 (encoding and sampling conventions).

The paper names no machine model. Programs are finite instruction lists over a memory of rational
cells indexed by `ℤ`, with
* exact rational arithmetic, floor, indirect load/store and a comparison jump;
* `coin`: a fair bit;
* `sample`: an exact draw from an explicitly given rational distribution (the convention of the
  rounding analyses, App. E.2); a program that never executes it is `CoinOnly`;
* `query`: one call to the oracle, a fixed function from question lists to answer lists;
* `halt`.
Every step is charged `1` plus the bit lengths of every address, operand, result, oracle
question and answer and sampled list it touches (the bit-cost model). The semantics is a
probability distribution (`PMF`) over machine states.

The input is in cells `0, 1, 2, …`; the output list is read after halting from the cells
`-2, -3, …`, its length from cell `-1` (`outList`).
-/

/-- Instructions; `i j l` are fixed cell addresses, `[i]` is the content of cell `i`. -/
inductive Instr where
  /-- `[i] := q`. -/
  | const (i : ℤ) (q : ℚ)
  /-- `[i] := [j] + [l]`. -/
  | add (i j l : ℤ)
  /-- `[i] := [j] - [l]`. -/
  | sub (i j l : ℤ)
  /-- `[i] := [j] * [l]`. -/
  | mul (i j l : ℤ)
  /-- `[i] := [j] / [l]` (with `q / 0 = 0`). -/
  | div (i j l : ℤ)
  /-- `[i] := ⌊[j]⌋`. -/
  | floor (i j : ℤ)
  /-- `[i] := [⌊[j]⌋]`. -/
  | load (i j : ℤ)
  /-- `[⌊[i]⌋] := [j]`. -/
  | store (i j : ℤ)
  /-- If `[i] < [j]`, jump to position `target`, otherwise continue. -/
  | jlt (i j : ℤ) (target : ℕ)
  /-- `[i] := 0` or `1`, each with probability `1/2` (a fair coin). -/
  | coin (i : ℤ)
  /-- Read the list `q_0, …, q_{k-1}` from the `k = ⌊[l]⌋` cells starting at `⌊[j]⌋`; if it is a
  probability distribution, `[i] := t` with probability `q_t`, otherwise `[i] := -1`. -/
  | sample (i j l : ℤ)
  /-- Ask the oracle the question read from the `k = ⌊[l]⌋` cells starting at `⌊[j]⌋`; the
  answer list `a` is written as `|a|, a_0, a_1, …` into the cells starting at `⌊[i]⌋`. -/
  | query (i j l : ℤ)
  /-- Stop. -/
  | halt
  deriving Inhabited

/-- A program is a finite instruction list; running past its end halts. -/
abbrev Program := List Instr

/-- The memory: one rational per integer address. -/
abbrev Memory := ℤ → ℚ

/-- An oracle: a fixed function from question lists to answer lists. -/
abbrev Oracle := List ℚ → List ℚ

/-- The oracle of a program without oracle access: every answer is empty. -/
def noOracle : Oracle := fun _ => []

/-- Bit length of a rational: bits of the numerator's absolute value plus bits of the
denominator. -/
def bitSizeQ (q : ℚ) : ℕ := Nat.size q.num.natAbs + Nat.size q.den

/-- Bit length of an integer. -/
def bitSizeZ (z : ℤ) : ℕ := Nat.size z.natAbs

/-- Encoding length of a list of rationals: one per entry plus the bit lengths of the entries. -/
def listBits (l : List ℚ) : ℕ := l.length + (l.map bitSizeQ).sum

/-- A machine state. `aborted` is set only by the capped sampler of App. E.2 (`stepCapped`). -/
structure State where
  /-- The position of the next instruction. -/
  pc : ℕ
  /-- The memory. -/
  mem : Memory
  /-- Whether the run has stopped. -/
  halted : Bool
  /-- Whether the run stopped because a capped sampling call failed. -/
  aborted : Bool
  /-- The bit-cost work spent so far. -/
  work : ℕ
  /-- The number of oracle calls so far. -/
  queries : ℕ
  /-- The number of sampling calls so far. -/
  samples : ℕ

/-- Write `q` into cell `i`. -/
def Memory.set (m : Memory) (i : ℤ) (q : ℚ) : Memory := fun x => if x = i then q else m x

/-- The `len` cells starting at `base`. -/
def readList (m : Memory) (base : ℤ) (len : ℕ) : List ℚ :=
  (List.range len).map (fun t => m (base + t))

/-- Write the list `l` into the cells starting at `base`. -/
def writeList (m : Memory) (base : ℤ) (l : List ℚ) : Memory :=
  fun x => if base ≤ x ∧ x < base + l.length then l.getD (x - base).toNat 0 else m x

open Classical in
/-- The exact law of a sampling call on the list `l`: index `t` with probability `l_t` when `l`
is a probability distribution (nonnegative entries summing to `1`), and the value `-1` with
certainty otherwise. -/
noncomputable def sampleLaw (l : List ℚ) : PMF ℤ :=
  if h : (∑ t : Fin l.length, ENNReal.ofReal ((l.get t : ℚ) : ℝ)) = 1 ∧ ∀ q ∈ l, 0 ≤ q then
    (PMF.ofFintype (fun t : Fin l.length => ENNReal.ofReal ((l.get t : ℚ) : ℝ)) h.1).map
      (fun t => (t : ℤ))
  else PMF.pure (-1)

/-- One step of program `P` with oracle `O`, where a sampling call on the list `l` draws from
`samp l` (`none` = the call aborts the run) and costs `sampCost l` on top of the bit lengths of
its addresses and operands. A halted state is absorbing. -/
noncomputable def stepWith (samp : List ℚ → PMF (Option ℤ)) (sampCost : List ℚ → ℕ)
    (P : Program) (O : Oracle) (s : State) : PMF State :=
  if s.halted then PMF.pure s else
  let m := s.mem
  let next (m' : Memory) (cost : ℕ) : State :=
    { s with pc := s.pc + 1, mem := m', work := s.work + 1 + cost }
  let arith (i j l : ℤ) (r : ℚ) : PMF State :=
    PMF.pure (next (m.set i r) (bitSizeZ i + bitSizeZ j + bitSizeZ l + bitSizeQ (m j) +
      bitSizeQ (m l) + bitSizeQ r))
  match P.getD s.pc Instr.halt with
  | .halt => PMF.pure { s with halted := true, work := s.work + 1 }
  | .const i q => PMF.pure (next (m.set i q) (bitSizeZ i + bitSizeQ q))
  | .add i j l => arith i j l (m j + m l)
  | .sub i j l => arith i j l (m j - m l)
  | .mul i j l => arith i j l (m j * m l)
  | .div i j l => arith i j l (m j / m l)
  | .floor i j =>
    let r : ℚ := (⌊m j⌋ : ℚ)
    PMF.pure (next (m.set i r) (bitSizeZ i + bitSizeZ j + bitSizeQ (m j) + bitSizeQ r))
  | .load i j =>
    let a := ⌊m j⌋
    PMF.pure (next (m.set i (m a))
      (bitSizeZ i + bitSizeZ j + bitSizeQ (m j) + bitSizeZ a + bitSizeQ (m a)))
  | .store i j =>
    let a := ⌊m i⌋
    PMF.pure (next (m.set a (m j))
      (bitSizeZ i + bitSizeZ j + bitSizeQ (m i) + bitSizeZ a + bitSizeQ (m j)))
  | .jlt i j t =>
    PMF.pure { s with pc := if m i < m j then t else s.pc + 1,
                      work := s.work + 1 + bitSizeZ i + bitSizeZ j + bitSizeQ (m i) +
                        bitSizeQ (m j) + Nat.size t }
  | .coin i =>
    (PMF.uniformOfFintype Bool).map
      (fun b => next (m.set i (if b then 1 else 0)) (bitSizeZ i))
  | .sample i j l =>
    let base := ⌊m j⌋
    let len := (⌊m l⌋).toNat
    let qs := readList m base len
    let cost := bitSizeZ i + bitSizeZ j + bitSizeZ l + bitSizeQ (m j) + bitSizeQ (m l) +
      listBits qs + sampCost qs
    (samp qs).map (fun o => match o with
      | some t => { next (m.set i (t : ℚ)) (cost + bitSizeZ t) with samples := s.samples + 1 }
      | none => { s with halted := true, aborted := true, work := s.work + 1 + cost,
                         samples := s.samples + 1 })
  | .query i j l =>
    let base := ⌊m j⌋
    let len := (⌊m l⌋).toNat
    let qs := readList m base len
    let ans := O qs
    let dst := ⌊m i⌋
    PMF.pure { next (writeList m dst ((ans.length : ℚ) :: ans))
                 (bitSizeZ i + bitSizeZ j + bitSizeZ l + bitSizeQ (m i) + bitSizeQ (m j) +
                   bitSizeQ (m l) + listBits qs + listBits ans) with
               queries := s.queries + 1 }

/-- One step with exact sampling (`sampleLaw`). -/
noncomputable def step (P : Program) (O : Oracle) (s : State) : PMF State :=
  stepWith (fun l => (sampleLaw l).map some) (fun _ => 0) P O s

/-- The law of the state after `k` steps from `s`. -/
noncomputable def runWith (stp : State → PMF State) : ℕ → State → PMF State
  | 0, s => PMF.pure s
  | k + 1, s => (stp s).bind (runWith stp k)

/-- The law of the state after `k` exact steps. -/
noncomputable def run (P : Program) (O : Oracle) (k : ℕ) (s : State) : PMF State :=
  runWith (step P O) k s

/-- The initial state on `input`: the input in cells `0, 1, 2, …`, zero elsewhere. -/
def initState (input : List ℚ) : State where
  pc := 0
  mem := fun a => if 0 ≤ a then input.getD a.toNat 0 else 0
  halted := false
  aborted := false
  work := 0
  queries := 0
  samples := 0

/-- The output list of a memory: length `⌊[-1]⌋`, entries `[-2], [-3], …`. -/
def outList (m : Memory) : List ℚ :=
  (List.range (⌊m (-1)⌋).toNat).map (fun t => m (-(t : ℤ) - 2))

/-- Every run of `P` with oracle `O` on `input` halts with work at most `B` (worst case over
all coin and sampling outcomes). Each step costs at least `1`, so such a run has halted after
`B + 1` steps. -/
def HaltsWithin (P : Program) (O : Oracle) (input : List ℚ) (B : ℕ) : Prop :=
  ∀ s ∈ (run P O (B + 1) (initState input)).support, s.halted = true ∧ s.work ≤ B

/-- The probability that a law satisfies `E`. -/
noncomputable def probOf {α : Type*} (μ : PMF α) (E : α → Prop) : ℝ :=
  (μ.toOuterMeasure {a | E a}).toReal

/-- The conditional probability `Pr[E | F] = Pr[E ∧ F] / Pr[F]`. -/
noncomputable def condProbOf {α : Type*} (μ : PMF α) (E F : α → Prop) : ℝ :=
  probOf μ (fun a => E a ∧ F a) / probOf μ F

/-- The probability that the output list of a run of `P` (with oracle `O`, on `input`, after
`B + 1` steps) satisfies `E`. When `HaltsWithin P O input B` holds, every run has halted by then
and this is the probability over the final outputs. -/
noncomputable def outProb (P : Program) (O : Oracle) (input : List ℚ) (B : ℕ)
    (E : List ℚ → Prop) : ℝ :=
  probOf (run P O (B + 1) (initState input)) (fun s => E (outList s.mem))

/-- The program never executes an exact sampling call: its only randomness is fair coins. -/
def CoinOnly (P : Program) : Prop :=
  ∀ ins ∈ P, ∀ i j l : ℤ, ins ≠ Instr.sample i j l

/-! ## Capped rejection sampling (App. E.2) -/

/-- The integer `∑_k r_k 2^k` written by the bits `r`. -/
def bitsToNat {b : ℕ} (r : Fin b → Bool) : ℕ := ∑ k : Fin b, if r k then 2 ^ (k : ℕ) else 0

/-- At most `T` rejection trials, each drawing `b` fair bits and accepting the resulting integer
if it is below `Q`; `none` if all `T` trials are rejected. -/
noncomputable def cappedReject (Q b : ℕ) : ℕ → PMF (Option ℕ)
  | 0 => PMF.pure none
  | T + 1 => (PMF.uniformOfFintype (Fin b → Bool)).bind fun r =>
      if bitsToNat r < Q then PMF.pure (some (bitsToNat r)) else cappedReject Q b T

/-- The common denominator `Q` of a list of rationals (lcm of the denominators). -/
def commonDen (l : List ℚ) : ℕ := (l.map Rat.den).foldr Nat.lcm 1

/-- The outcome index assigned to the accepted integer `r ∈ {0, …, Q-1}`: the number of
`t` with `Q · (l_0 + ⋯ + l_t) ≤ r`, i.e. outcome `t` gets the `Q · l_t` integers of its block. -/
def bucket (l : List ℚ) (Q r : ℕ) : ℤ :=
  (((List.range l.length).filter fun t => (Q : ℚ) * (l.take (t + 1)).sum ≤ (r : ℚ)).length : ℤ)

/-- The capped sampler of App. E.2 with `T` trials per call: rejection sampling with
`⌈log₂ Q⌉` fair bits per trial, `Q` the common denominator; `none` = abort. On a list that is not
a probability distribution it returns `-1`, as the exact sampler does. -/
noncomputable def cappedSample (T : ℕ) (l : List ℚ) : PMF (Option ℤ) :=
  if (∀ q ∈ l, 0 ≤ q) ∧ l.sum = 1 then
    (cappedReject (commonDen l) (Nat.clog 2 (commonDen l)) T).map
      (Option.map (bucket l (commonDen l)))
  else PMF.pure (some (-1))

/-- One step in which every sampling call is run by the capped sampler with `T` trials, charged
`T · (1 + ⌈log₂ Q⌉)` extra work for its `T` trials of `⌈log₂ Q⌉` bits. -/
noncomputable def stepCapped (T : ℕ) (P : Program) (O : Oracle) (s : State) : PMF State :=
  stepWith (cappedSample T) (fun l => T * (1 + Nat.clog 2 (commonDen l))) P O s

/-- The law of the state after `k` capped steps. -/
noncomputable def runCapped (T : ℕ) (P : Program) (O : Oracle) (k : ℕ) (s : State) :
    PMF State :=
  runWith (stepCapped T P O) k s

end SantaClausNSW.MaxMin



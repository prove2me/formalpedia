-- Prove2me | Definitions.Def_AlgoPFR_Machine
-- name    : AlgoPFR_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:48.938997+00:00
-- url     : https://prove2.me/theorems/a051e6ef-9f26-4aef-9a0a-0e4c54e3a947
-- title:
--   The randomized log-cost oracle RAM, its tapes, and the success predicate of Theorem 1.2
-- statement:
--   This fixes what "time" means in the headline theorem. The machine is a **randomized log-cost integer RAM**: natural-number memory with indirect addressing, arithmetic and bitwise instructions, conditional jumps, and three random sources.
--
--   1. A **coin** instruction reads the next fair bit.
--   2. A **sample** instruction reads the next element of an i.i.d. stream from a law $p$ on $\mathbb F_2^n$.
--   3. A **query** instruction on a vector $x$ answers the $k$-th time with $u_k<r(x)$, where the $u_k$ are i.i.d. uniform on $[0,1)$; this is a density coin of rate $r$. For $r=1_A$ it is the exact membership oracle of $A$ on every possible tape.
--
--   Each instruction costs $1$ plus the bit lengths of everything it touches, addresses included; a sample or a query costs a further $n$. Counters record the number of samples and queries.
--
--   An output **succeeds** for $(A,K)$ with constants $C,c$ when it encodes a linearly independent list $L$ with $|\mathrm{span}\,L|\le|A|$, and there is a set $T$ with $|T|\le CK^c$ and $A\subseteq\bigcup_{t\in T}(t+\mathrm{span}\,L)$.
--
--   "With probability at least $q$" means that the event contains a measurable event of measure at least $q$.
--
--   **Formalization Note** The source names no machine model. A unit-cost RAM on unbounded integers can compute beyond polynomial time by repeated squaring, which would weaken the existence of a fast program, so bit lengths are charged. Polynomial time on this machine is the same class as polynomial time on a Turing machine with these oracles. Vectors are encoded as $n$-bit naturals.
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Theorem 1.2, p.2 (the model is the formalization's choice; the source names none)

import Mathlib
import Definitions.Def_AlgoPFR_rd

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace AlgoPFR

noncomputable section

/-- The instruction set of the **randomized log-cost oracle RAM** that fixes the word "time" in
Theorem 1.2, p.2 of arXiv:2609.20771 (sha256 60e45066…). Operands are memory addresses; `lit` writes a
literal.

**Formalization Note.** The paper names no machine model. The model follows the pattern of the
published RAMs (`FasterSFM.Machine`, `HMBinPacking.OracleMachine`) but charges bit lengths. A
unit-cost RAM on unbounded integers may compute beyond polynomial time by repeated squaring, which
would make the existence of a fast program a weaker claim. Polynomial time on a log-cost RAM is the
same class as polynomial time on a Turing machine. -/
inductive Instr
  /-- `mem[d] := v`. -/
  | lit (d v : ℕ)
  /-- `mem[d] := mem[s]`. -/
  | copy (d s : ℕ)
  /-- `mem[d] := mem[a] + mem[b]`. -/
  | add (d a b : ℕ)
  /-- `mem[d] := mem[a] - mem[b]`, truncated at `0`. -/
  | sub (d a b : ℕ)
  /-- `mem[d] := mem[a] * mem[b]`. -/
  | mul (d a b : ℕ)
  /-- `mem[d] := mem[a] / mem[b]`, with Lean's `x / 0 = 0`. -/
  | div (d a b : ℕ)
  /-- `mem[d] := mem[a] % mem[b]`. -/
  | mod (d a b : ℕ)
  /-- `mem[d] :=` bitwise xor of `mem[a]`, `mem[b]`. -/
  | xor (d a b : ℕ)
  /-- `mem[d] :=` bitwise and of `mem[a]`, `mem[b]`. -/
  | land (d a b : ℕ)
  /-- `mem[d] := mem[a] * 2 ^ mem[b]`. -/
  | shl (d a b : ℕ)
  /-- `mem[d] := mem[a] / 2 ^ mem[b]`. -/
  | shr (d a b : ℕ)
  /-- `mem[d] := mem[mem[a]]`. -/
  | load (d a : ℕ)
  /-- `mem[mem[a]] := mem[s]`. -/
  | store (a s : ℕ)
  /-- Jump to `t` if `mem[a] = mem[b]`. -/
  | jeq (a b t : ℕ)
  /-- Jump to `t` if `mem[a] ≤ mem[b]`. -/
  | jle (a b t : ℕ)
  /-- `mem[d] :=` the next fair coin, `0` or `1`. -/
  | coin (d : ℕ)
  /-- `mem[d] :=` the encoding of the next element of the sample stream. -/
  | sample (d : ℕ)
  /-- `mem[d] :=` the answer `0` or `1` of the density-coin oracle on the vector encoded by `mem[s]`
  (`0` if `mem[s]` encodes no vector of `F₂ⁿ`). -/
  | query (d s : ℕ)
  /-- Halt with output `mem[s], …, mem[s + ℓ - 1]`. -/
  | halt (s ℓ : ℕ)

/-- A program is a finite list of instructions. It may contain arbitrary constants, but has no
access to `n`, `A`, `K` or `δ` other than through its input and its oracles. -/
abbrev Program := List Instr

/-- A machine state. -/
structure MState where
  /-- The program counter. -/
  pc : ℕ
  /-- The memory; unwritten cells hold `0`. -/
  mem : ℕ → ℕ
  /-- The number of fair coins read so far. -/
  coins : ℕ
  /-- The number of `sample` instructions executed so far. -/
  samples : ℕ
  /-- The number of `query` instructions executed so far. -/
  queries : ℕ
  /-- The log-cost time charged so far. -/
  cost : ℕ
  /-- The output, once the machine has halted. -/
  out : Option (List ℕ)

/-- The input convention: the list of naturals in cells `0, 1, …`, everything else `0`. -/
def initState (input : List ℕ) : MState :=
  ⟨0, fun i => input.getD i 0, 0, 0, 0, 0, none⟩

/-- Vectors of `F₂ⁿ` as `n`-bit naturals: coordinate `i` is bit `i`. -/
def encodeVec {n : ℕ} (x : Vec n) : ℕ :=
  Nat.ofBits fun i => decide (x i = 1)

/-- The inverse of `encodeVec` on `{k | k < 2 ^ n}`. -/
def decodeVec (n k : ℕ) : Vec n :=
  fun i => if k.testBit i.val then 1 else 0

/-- The three random tapes: fair coins, the sample stream, and the uniforms `u_k` behind the
density-coin oracle. -/
abbrev Tape (n : ℕ) := (ℕ → Bool) × (ℕ → Vec n) × (ℕ → ℝ)

/-- The bit length of a natural number, `Nat.size 0 = 0`. -/
abbrev bits (x : ℕ) : ℕ := Nat.size x

/-- Writes `v` into cell `d`, advances the program counter and charges `c`. -/
def MState.write (s : MState) (d v c : ℕ) : MState :=
  { s with pc := s.pc + 1, mem := Function.update s.mem d v, cost := s.cost + c }

/-- The charged binary operation `mem[d] := g mem[a] mem[b]`: one, plus the bit lengths of the three
addresses, the two operands and the result. -/
def MState.binop (s : MState) (g : ℕ → ℕ → ℕ) (d a b : ℕ) : MState :=
  let v := g (s.mem a) (s.mem b)
  s.write d v (1 + bits d + bits a + bits b + bits (s.mem a) + bits (s.mem b) + bits v)

/-- The charged conditional jump. -/
def MState.branch (s : MState) (c : Prop) [Decidable c] (a b t : ℕ) : MState :=
  { s with
    pc := if c then t else s.pc + 1
    cost := s.cost + (1 + bits a + bits b + bits t + bits (s.mem a) + bits (s.mem b)) }

open Classical in
/-- One instruction. `r` is the density-coin rate: the `k`-th query on `x` answers
`decide (u k < r x)`, which is a Bernoulli variable with parameter `r x` when `u k` is uniform on
`[0, 1)` and `0 ≤ r x ≤ 1`.

**Formalization Note.** Each instruction costs `1` plus the bit lengths of every operand and result
it touches, addresses included. `sample` and `query` cost `n + 1` on top of their address bits, since
an oracle exchange transports an `n`-bit vector. -/
def exec (n : ℕ) (r : Vec n → ℝ) (ω : Tape n) (i : Instr) (s : MState) : MState :=
  match i with
  | .lit d v => s.write d v (1 + bits d + bits v)
  | .copy d a => s.write d (s.mem a) (1 + bits d + bits a + bits (s.mem a))
  | .add d a b => s.binop (· + ·) d a b
  | .sub d a b => s.binop (· - ·) d a b
  | .mul d a b => s.binop (· * ·) d a b
  | .div d a b => s.binop (· / ·) d a b
  | .mod d a b => s.binop (· % ·) d a b
  | .xor d a b => s.binop Nat.xor d a b
  | .land d a b => s.binop Nat.land d a b
  | .shl d a b => s.binop Nat.shiftLeft d a b
  | .shr d a b => s.binop Nat.shiftRight d a b
  | .load d a =>
    s.write d (s.mem (s.mem a))
      (1 + bits d + bits a + bits (s.mem a) + bits (s.mem (s.mem a)))
  | .store a b =>
    s.write (s.mem a) (s.mem b) (1 + bits a + bits b + bits (s.mem a) + bits (s.mem b))
  | .jeq a b t => s.branch (s.mem a = s.mem b) a b t
  | .jle a b t => s.branch (s.mem a ≤ s.mem b) a b t
  | .coin d =>
    { s.write d (if ω.1 s.coins then 1 else 0) (2 + bits d) with coins := s.coins + 1 }
  | .sample d =>
    { s.write d (encodeVec (ω.2.1 s.samples)) (n + 1 + bits d) with samples := s.samples + 1 }
  | .query d a =>
    let answer : Bool :=
      if s.mem a < 2 ^ n then decide (ω.2.2 s.queries < r (decodeVec n (s.mem a))) else false
    { s.write d (if answer then 1 else 0) (n + 1 + bits d + bits a + bits (s.mem a)) with
      queries := s.queries + 1 }
  | .halt a ℓ =>
    let o := (List.range ℓ).map fun i => s.mem (a + i)
    { s with
      out := some o
      cost := s.cost + (1 + bits a + bits ℓ + (o.map bits).sum) }

/-- One machine step. A halted machine stutters at zero cost; a program counter outside the program
is stuck and keeps being charged, so a program cannot halt by running off its end. -/
def step (n : ℕ) (P : Program) (r : Vec n → ℝ) (ω : Tape n) (s : MState) : MState :=
  match s.out with
  | some _ => s
  | none =>
    match P[s.pc]? with
    | none => { s with cost := s.cost + 1 }
    | some i => exec n r ω i s

/-- The state after `t` steps on the given input. -/
def run (n : ℕ) (P : Program) (r : Vec n → ℝ) (input : List ℕ) (ω : Tape n) (t : ℕ) : MState :=
  (step n P r ω)^[t] (initState input)

/-- On the tape `ω` the machine halts with output `o`. -/
def Outputs (n : ℕ) (P : Program) (r : Vec n → ℝ) (input : List ℕ) (ω : Tape n)
    (o : List ℕ) : Prop :=
  ∃ t, (run n P r input ω t).out = some o

/-- On the tape `ω` the machine halts, and at the halting step its log-cost time, its number of
samples and its number of queries are each at most `B`. -/
def HaltsWithin (n : ℕ) (P : Program) (r : Vec n → ℝ) (input : List ℕ) (ω : Tape n)
    (B : ℝ) : Prop :=
  ∃ t, (run n P r input ω t).out.isSome ∧ ((run n P r input ω t).cost : ℝ) ≤ B ∧
    ((run n P r input ω t).samples : ℝ) ≤ B ∧ ((run n P r input ω t).queries : ℝ) ≤ B

/-- The law of the uniforms `u_k`: Lebesgue measure on `[0, 1)`. -/
def unitLaw : Measure ℝ := volume.restrict (Set.Ico 0 1)

instance : IsProbabilityMeasure unitLaw :=
  ⟨by simp [unitLaw]⟩

/-- The probability measure on tapes: i.i.d. fair coins, an i.i.d. sample stream with law `p`, and
i.i.d. uniforms on `[0, 1)`, all independent. -/
def tapeMeasure {n : ℕ} (p : PMF (Vec n)) : Measure (Tape n) :=
  (Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure).prod
    ((Measure.infinitePi fun _ : ℕ => p.toMeasure).prod
      (Measure.infinitePi fun _ : ℕ => unitLaw))

/-- "With probability at least `q`": the event contains a measurable event of measure at least `q`.

**Formalization Note.** This is the inner-measure form, which needs no measurability proof of the
event and is not weakened by an outer measure on a non-measurable set. -/
def ProbAtLeast {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (S : Set Ω) (q : ℝ) : Prop :=
  ∃ E, MeasurableSet E ∧ E ⊆ S ∧ ENNReal.ofReal q ≤ μ E

open Classical in
/-- The density-coin rate of the membership oracle of `A`: `1_A`. -/
def memberRate {n : ℕ} (A : Finset (Vec n)) (x : Vec n) : ℝ :=
  if x ∈ A then 1 else 0

/-- A tape is possible for the oracles of `A`: every sample lies in `A` and every uniform lies in
`[0, 1)`. On such a tape the `query` instruction answers exactly `x ∈ A`. -/
def IsRunTape {n : ℕ} (A : Finset (Vec n)) (ω : Tape n) : Prop :=
  (∀ k, ω.2.1 k ∈ A) ∧ ∀ k, ω.2.2 k ∈ Set.Ico (0 : ℝ) 1

/-- The subspace spanned by a list of vectors. -/
def listSpan {n : ℕ} (L : List (Vec n)) : Submodule (ZMod 2) (Vec n) :=
  Submodule.span (ZMod 2) {x | x ∈ L}

/-- "Outputs a basis": the list is linearly independent, so it is a basis of its span. -/
def IsBasisList {n : ℕ} (L : List (Vec n)) : Prop :=
  LinearIndependent (ZMod 2) (fun i : Fin L.length => L.get i)

open Classical in
/-- `|A ∩ (a + V)|`. -/
def cosetCount {n : ℕ} (A : Finset (Vec n)) (a : Vec n) (V : Submodule (ZMod 2) (Vec n)) : ℕ :=
  (A.filter fun x => x - a ∈ V).card

/-- `|V|`. -/
def subspaceCard {n : ℕ} (V : Submodule (ZMod 2) (Vec n)) : ℕ :=
  Nat.card V

/-- The success predicate of Theorem 1.2, p.2: the output encodes a basis `L` of a subspace `V` with
`|V| ≤ |A|`, and `A` is covered by at most `C · K^c` translates of `V`. -/
def IsPFROutput {n : ℕ} (A : Finset (Vec n)) (K C : ℝ) (c : ℕ) (o : List ℕ) : Prop :=
  ∃ L : List (Vec n), o = L.map encodeVec ∧ IsBasisList L ∧
    subspaceCard (listSpan L) ≤ A.card ∧
    ∃ T : Finset (Vec n), (T.card : ℝ) ≤ C * K ^ c ∧ ∀ a ∈ A, ∃ t ∈ T, a - t ∈ listSpan L

end

end AlgoPFR



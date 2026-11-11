-- Prove2me | Definitions.Def_PrefixMixLearn_Proper_Machine
-- name    : PrefixMixLearn_Proper_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:45:21.246743+00:00
-- url     : https://prove2.me/theorems/6143425f-d227-466c-9e5b-868cc730e418
-- title:
--   The fair-coin log-cost RAM with a prefix-conditional oracle $\mathrm{COND}_P$, its run law and cost, and the input/output encodings
-- statement:
--   The paper names no machine model; its algorithms are charged for bit operations, query writing, response processing, random bits, output length and input reading, and use **fair bits** as randomness. The model here is a log-cost RAM over natural numbers: arithmetic, bitwise, shift, load/store and jump instructions, a **fair coin** instruction writing one uniformly random bit, a **query** instruction that sends a list of memory cells to an oracle and writes its (freshly random) reply, and **halt** with an output list. Each instruction costs one plus the bit lengths of everything it touches; a query is charged for every cell it reads and writes, halt for every output cell. A run's law is over the coins and the oracle replies; a halted machine stays halted at no cost.
--
--   The **prefix-conditional oracle** $\mathrm{COND}_P$ of a law $P$ on $\{0,1\}^T$ (Definition 2.1): a prefix $h\in\{0,1\}^{|h|}$ with $0\le|h|<T$ returns a fresh suffix $f\in\{0,1\}^{T-|h|}$ with law $P_h(f)=P(hf)/P[h]$, with fresh randomness conditionally on the history. A query that is not such a prefix (or has zero mass) gets the empty reply. A pair oracle answers $b::h$ by $\mathrm{COND}_{F_b}$ at $h$, $b\in\{0,1\}$. The selector oracle of Theorem B.4 answers $0::h$ by $\mathrm{COND}_P$ at $h$ and $1::i::x$ by the exact rational density $M_{i+1}(x)$ of a candidate, as (numerator, denominator).
--
--   **Encodings** (Appendix B.1). A positive rational is the pair (numerator, denominator); the input length is the total bit length. A dyadic product is $[B,k_1,\dots,k_T]$ with means $k_i2^{-B}$; a dyadic two-mixture is $[B,k^0,k^1,j]$ with law $(1-j2^{-B})Q_{k^02^{-B}}+j2^{-B}Q_{k^12^{-B}}$; it is **proper** when $B\ge1$, $j\le 2^B$ and both mean vectors lie in $[\alpha,1-\alpha]^T$ (so its law is in $\mathcal M_{2,\alpha,T}$). `HaltsWithin` says that on every run the cost stays below a bound $B$ and the machine has halted by time $B$; `OutputsSatisfy`, `QueriesWithin`, `QueryCountWhere` say that every run's output, number of calls, or exact number of calls of a given kind at halting is as stated; `densBits` is the largest bit length of a candidate density value; `outProb` is the probability of halting with an output in a given set.
--
--   **Formalization Note.** Patterned on the published `PDSEquiv_Machine`, but with a fair coin in place of its exact $\mathrm{Ber}(a/b)$ draw, which would give an algorithm more power than the paper's fair bits.
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 3 (PDF 5), Definition 2.1; p. 4 (PDF 6), §2; p. 17 (PDF 19), App. B.1

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace PrefixMixLearn.Proper

/-!
# The fair-coin log-cost RAM with a prefix-conditional oracle, input and output encodings

Saravanan, *Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional
Samples*, STOC 2027 submission (manuscript sha256 9c359910…), Definition 2.1, p. 3 (PDF 5);
§2, p. 4 (PDF 6); Appendix B.1, p. 17 (PDF 19).

**Reading.** The paper names no machine. It counts "bit operations, query writing, response
processing, random bits, output length, and input reading" (p. 4), and learner randomness is
"independent fair bits" (p. 17). This is a log-cost RAM with natural-number words on the pattern of
the published `PDSEquiv.Machine`, but its only random instruction is a **fair coin** `coin`; there
is no exact `Ber(a/b)` draw. Every instruction is charged one plus the bit lengths of the addresses,
operands and results it touches; `query` is charged for every cell of the query it reads and every
cell of the reply it writes, and `halt` for every output cell. So one bound on the log-cost bounds
the oracle calls, written and returned symbols, coins, bit time and output length.

* Registers `reg` and memory `mem` hold naturals; the input list sits in `mem` from cell `0`.
* `query d s l` sends the cells `mem[reg s], …, mem[reg s + reg l − 1]` to the oracle; the reply `r`
  (fresh randomness) is written as `mem[reg d] := r.length` followed by `r`.
* A halted machine stutters at no cost; a program counter outside the program is stuck and keeps
  being charged, so a program cannot halt by running off its end.

**The oracle `COND_P` (Definition 2.1).** A query is a list `h` of cells. If `h` is a 0/1 list with
`|h| < T` (and the prefix has positive mass, which full support guarantees), the reply is a fresh
suffix `f ∈ {0,1}^{T − |h|}` (as a 0/1 list) with law `P_h(f) = P(hf)/P[h]`; each call uses fresh
randomness, conditionally on the whole history. Any other query (not 0/1, `|h| ≥ T`, or a zero-mass
prefix) gets the empty reply, which carries no information about `P`.

**Encodings.** A positive rational `q` is the two cells `[num, den]` (lowest terms, binary
naturals); `encLen` is the total bit length of an input. A dyadic product is
`[B, k_1, …, k_T]` with means `k_i 2^{-B}`; a dyadic two-mixture is `[B, k⁰_1…k⁰_T, k¹_1…k¹_T, j]`
with law `(1 − j 2^{-B}) Q_{k⁰ 2^{-B}} + j 2^{-B} Q_{k¹ 2^{-B}}` (Appendix B.1).
-/

/-- The instruction set. Operands are register numbers. -/
inductive Instr
  /-- `reg[d] := v`. -/
  | lit (d v : ℕ)
  /-- `reg[d] := reg[s]`. -/
  | copy (d s : ℕ)
  /-- `reg[d] := reg[a] + reg[b]`. -/
  | add (d a b : ℕ)
  /-- `reg[d] := reg[a] - reg[b]`, truncated at `0`. -/
  | sub (d a b : ℕ)
  /-- `reg[d] := reg[a] * reg[b]`. -/
  | mul (d a b : ℕ)
  /-- `reg[d] := reg[a] / reg[b]`, with `x / 0 = 0`. -/
  | div (d a b : ℕ)
  /-- `reg[d] := reg[a] % reg[b]`. -/
  | mod (d a b : ℕ)
  /-- `reg[d] :=` bitwise xor of `reg[a]`, `reg[b]`. -/
  | xor (d a b : ℕ)
  /-- `reg[d] :=` bitwise and of `reg[a]`, `reg[b]`. -/
  | land (d a b : ℕ)
  /-- `reg[d] := reg[a] * 2 ^ reg[b]`. -/
  | shl (d a b : ℕ)
  /-- `reg[d] := reg[a] / 2 ^ reg[b]`. -/
  | shr (d a b : ℕ)
  /-- `reg[d] := mem[reg[a]]`. -/
  | load (d a : ℕ)
  /-- `mem[reg[a]] := reg[s]`. -/
  | store (a s : ℕ)
  /-- Jump to instruction `t` if `reg[a] = reg[b]`. -/
  | jeq (a b t : ℕ)
  /-- Jump to instruction `t` if `reg[a] ≤ reg[b]`. -/
  | jle (a b t : ℕ)
  /-- `reg[d] :=` a fresh fair bit (`0` or `1`, each with probability `1/2`). -/
  | coin (d : ℕ)
  /-- Query the oracle on `mem[reg[s]], …, mem[reg[s] + reg[l] - 1]`; the reply `r` (fresh
  randomness) is written as `mem[reg[d]] := r.length` and `r` to the cells after it. -/
  | query (d s l : ℕ)
  /-- Halt with output `mem[reg[s]], …, mem[reg[s] + reg[l] - 1]`. -/
  | halt (s l : ℕ)

/-- A program is a finite list of instructions, the same for every input. -/
abbrev Program := List Instr

/-- A machine state. -/
structure MState where
  /-- The program counter. -/
  pc : ℕ
  /-- The registers; unwritten registers hold `0`. -/
  reg : ℕ → ℕ
  /-- The memory; unwritten cells hold `0`. -/
  mem : ℕ → ℕ
  /-- The log-cost time charged so far. -/
  cost : ℕ
  /-- The oracle queries made so far, oldest first. -/
  queries : List (List ℕ)
  /-- The output, once the machine has halted. -/
  out : Option (List ℕ)

/-- The input convention: the list of naturals in memory cells `0, 1, …`, everything else `0`. -/
def initState (input : List ℕ) : MState :=
  ⟨0, fun _ => 0, fun i => input.getD i 0, 0, [], none⟩

/-- The bit length of a natural number, `Nat.size 0 = 0`. -/
abbrev bits (x : ℕ) : ℕ := Nat.size x

/-- An oracle: a query (a list of cells) and a fresh draw of a reply (a list of cells). -/
abbrev Oracle := List ℕ → PMF (List ℕ)

/-- Reads `l` consecutive memory cells from `a`. -/
def MState.readCells (s : MState) (a l : ℕ) : List ℕ :=
  (List.range l).map fun i => s.mem (a + i)

/-- The log-cost of reading `l` consecutive memory cells from `a`. -/
def MState.readCost (s : MState) (a l : ℕ) : ℕ :=
  ((List.range l).map fun i => 1 + bits (a + i) + bits (s.mem (a + i))).sum

/-- Advances the program counter and charges `c`. -/
def MState.tick (s : MState) (c : ℕ) : MState :=
  { s with pc := s.pc + 1, cost := s.cost + c }

/-- Writes `v` into register `d`, advances and charges `c`. -/
def MState.setReg (s : MState) (d v c : ℕ) : MState :=
  { s.tick c with reg := Function.update s.reg d v }

/-- The charged binary operation `reg[d] := g reg[a] reg[b]`. -/
def MState.binop (s : MState) (g : ℕ → ℕ → ℕ) (d a b : ℕ) : MState :=
  let v := g (s.reg a) (s.reg b)
  s.setReg d v (1 + bits d + bits a + bits b + bits (s.reg a) + bits (s.reg b) + bits v)

/-- The charged conditional jump. -/
def MState.branch (s : MState) (c : Prop) [Decidable c] (a b t : ℕ) : MState :=
  { s with
    pc := if c then t else s.pc + 1
    cost := s.cost + (1 + bits a + bits b + bits t + bits (s.reg a) + bits (s.reg b)) }

/-- Writes the oracle's reply `r` at `a`: its length, then its entries. -/
def writeReply (m : ℕ → ℕ) (a : ℕ) (r : List ℕ) : ℕ → ℕ :=
  fun i =>
    if i = a then r.length
    else if a < i ∧ i ≤ a + r.length then r.getD (i - a - 1) 0
    else m i

/-- One executed instruction. Only `coin` and `query` draw randomness. -/
def stepInstr (Q : Oracle) (i : Instr) (s : MState) : PMF MState :=
  match i with
  | .lit d v => PMF.pure (s.setReg d v (1 + bits d + bits v))
  | .copy d a => PMF.pure (s.setReg d (s.reg a) (1 + bits d + bits a + bits (s.reg a)))
  | .add d a b => PMF.pure (s.binop (· + ·) d a b)
  | .sub d a b => PMF.pure (s.binop (· - ·) d a b)
  | .mul d a b => PMF.pure (s.binop (· * ·) d a b)
  | .div d a b => PMF.pure (s.binop (· / ·) d a b)
  | .mod d a b => PMF.pure (s.binop (· % ·) d a b)
  | .xor d a b => PMF.pure (s.binop Nat.xor d a b)
  | .land d a b => PMF.pure (s.binop Nat.land d a b)
  | .shl d a b => PMF.pure (s.binop Nat.shiftLeft d a b)
  | .shr d a b => PMF.pure (s.binop Nat.shiftRight d a b)
  | .load d a =>
    PMF.pure (s.setReg d (s.mem (s.reg a))
      (1 + bits d + bits a + bits (s.reg a) + bits (s.mem (s.reg a))))
  | .store a b =>
    PMF.pure { s.tick (1 + bits a + bits b + bits (s.reg a) + bits (s.reg b)) with
      mem := Function.update s.mem (s.reg a) (s.reg b) }
  | .jeq a b t => PMF.pure (s.branch (s.reg a = s.reg b) a b t)
  | .jle a b t => PMF.pure (s.branch (s.reg a ≤ s.reg b) a b t)
  | .coin d =>
    (PMF.uniformOfFintype Bool).map fun c => s.setReg d (if c then 1 else 0) (2 + bits d)
  | .query d a l =>
    let q := s.readCells (s.reg a) (s.reg l)
    (Q q).map fun r =>
      { s.tick (1 + bits d + bits a + bits l + bits (s.reg d) + bits (s.reg a) + bits (s.reg l)
            + s.readCost (s.reg a) (s.reg l) + bits r.length
            + (r.map fun v => 1 + bits (s.reg d + r.length) + bits v).sum) with
        mem := writeReply s.mem (s.reg d) r
        queries := s.queries ++ [q] }
  | .halt a l =>
    PMF.pure
      { s with
        out := some (s.readCells (s.reg a) (s.reg l))
        cost := s.cost + (1 + bits a + bits l + bits (s.reg a) + bits (s.reg l)
            + s.readCost (s.reg a) (s.reg l)) }

/-- One machine step. A halted machine stutters at zero cost; a program counter outside the program
is stuck and keeps being charged. -/
def step (Q : Oracle) (P : Program) (s : MState) : PMF MState :=
  match s.out with
  | some _ => PMF.pure s
  | none =>
    match P[s.pc]? with
    | none => PMF.pure { s with cost := s.cost + 1 }
    | some i => stepInstr Q i s

/-- The law of the machine state after `t` steps (over the fair coins and the oracle replies). -/
def runLaw (P : Program) (Q : Oracle) (input : List ℕ) : ℕ → PMF MState
  | 0 => PMF.pure (initState input)
  | t + 1 => (runLaw P Q input t).bind (step Q P)

/-- The probability that the machine halts with an output satisfying `E`. -/
def outProb (P : Program) (Q : Oracle) (input : List ℕ) (E : List ℕ → Prop) : ℝ :=
  (⨆ t, (runLaw P Q input t).toOuterMeasure {s | ∃ o, s.out = some o ∧ E o}).toReal

/-- On every run (every coin and every oracle reply), at every time, the log-cost is at most `B`,
and the machine has halted by time `B`. -/
def HaltsWithin (P : Program) (Q : Oracle) (input : List ℕ) (B : ℝ) : Prop :=
  ∀ t, ∀ s ∈ (runLaw P Q input t).support, (s.cost : ℝ) ≤ B ∧ (B ≤ t → s.out.isSome = true)

/-- On every run, at every time, at most `n` oracle calls have been made. -/
def QueriesWithin (P : Program) (Q : Oracle) (input : List ℕ) (n : ℝ) : Prop :=
  ∀ t, ∀ s ∈ (runLaw P Q input t).support, (s.queries.length : ℝ) ≤ n

/-- On every run, once halted, exactly `n` of the oracle calls made satisfy `kind` (e.g. the
target calls `0 :: h` of a selector). -/
def QueryCountWhere (P : Program) (Q : Oracle) (input : List ℕ) (kind : List ℕ → Prop) (n : ℕ) :
    Prop :=
  ∀ t, ∀ s ∈ (runLaw P Q input t).support, s.out.isSome = true →
    (s.queries.filter fun q => decide (kind q)).length = n

/-- On every run, once halted, the output satisfies `form`. -/
def OutputsSatisfy (P : Program) (Q : Oracle) (input : List ℕ) (form : List ℕ → Prop) : Prop :=
  ∀ t, ∀ s ∈ (runLaw P Q input t).support, ∀ o, s.out = some o → form o

/-! ## The prefix-conditional oracle -/

/-- A law on the cube as a `PMF` (the point mass at the all-zero string if `P` is not a law). -/
def lawPMF {T : ℕ} (P : Cube T → ℝ) : PMF (Cube T) :=
  if h : ∑ x, ENNReal.ofReal (P x) = 1 then PMF.ofFintype (fun x => ENNReal.ofReal (P x)) h
  else PMF.pure (fun _ => false)

/-- `y` extends the 0/1 prefix `h`: its first `|h|` bits are `h`. -/
def ExtendsPrefix {T : ℕ} (y : Cube T) (h : List ℕ) : Prop :=
  ∀ i : Fin T, i.val < h.length → h.getD i.val 0 = (if y i then 1 else 0)

/-- The suffix of `y` after its first `k` bits, as a 0/1 list of length `T − k`. -/
def suffixList {T : ℕ} (y : Cube T) (k : ℕ) : List ℕ :=
  ((List.finRange T).drop k).map fun i => if y i then 1 else 0

/-- The prefix-conditional oracle `COND_P` (Definition 2.1): a 0/1 prefix `h` with `|h| < T` and
positive mass gets a fresh suffix with law `P_h(f) = P(hf)/P[h]`; every other query gets `[]`. -/
def condOracle {T : ℕ} (P : Cube T → ℝ) : Oracle := fun h =>
  if hq : h.length < T ∧ (∀ b ∈ h, b ≤ 1) ∧
      ∃ y ∈ {y : Cube T | ExtendsPrefix y h}, y ∈ (lawPMF P).support then
    ((lawPMF P).filter {y | ExtendsPrefix y h} hq.2.2).map fun y => suffixList y h.length
  else PMF.pure []

/-- Two prefix-conditional oracles behind one query instruction: `0 :: h` asks `COND_{F_0}` at
`h`, `1 :: h` asks `COND_{F_1}` at `h`; every other query gets `[]`. -/
def pairOracle {d : ℕ} (F0 F1 : Cube d → ℝ) : Oracle := fun q =>
  match q with
  | [] => PMF.pure []
  | b :: h => if b = 0 then condOracle F0 h else if b = 1 then condOracle F1 h else PMF.pure []

/-- The selector's oracle for Theorem B.4: `0 :: h` asks the target oracle `COND_P` at `h`;
`1 :: i :: x` with `i < N` and `x` a 0/1 list of length `T` returns the exact rational density
`M_{i+1}(x)` as the two cells `[numerator, denominator]` (an exact candidate-density evaluation);
every other query gets `[]`. -/
def selectorOracle {T N : ℕ} (P : Cube T → ℝ) (Ms : Fin N → Cube T → ℚ) : Oracle := fun q =>
  match q with
  | 0 :: h => condOracle P h
  | 1 :: i :: xs =>
    if hi : i < N ∧ xs.length = T ∧ ∀ b ∈ xs, b ≤ 1 then
      PMF.pure [(Ms ⟨i, hi.1⟩ (fun j => xs.getD j.val 0 = 1)).num.toNat,
        (Ms ⟨i, hi.1⟩ (fun j => xs.getD j.val 0 = 1)).den]
    else PMF.pure []
  | _ => PMF.pure []

/-! ## Encodings -/

/-- A positive rational as the two cells `[numerator, denominator]` (lowest terms). -/
def ratCells (q : ℚ) : List ℕ := [q.num.toNat, q.den]

/-- The total bit length of an input: `Σ (bits v + 1)`. -/
def encLen (input : List ℕ) : ℕ := (input.map fun v => bits v + 1).sum

/-- A point of the cube as a 0/1 list. -/
def cubeCells {d : ℕ} (x : Cube d) : List ℕ := (List.finRange d).map fun i => if x i then 1 else 0

/-- A dyadic product code: precision `B` and numerators `k_i` (means `k_i 2^{-B}`). -/
structure ProdCode (T : ℕ) where
  /-- The precision `B`. -/
  prec : ℕ
  /-- The numerators. -/
  k : Fin T → ℕ

/-- A dyadic two-mixture code: common precision `B`, numerator vectors `k⁰` (component `ν`, weight
`1 − ŵ`) and `k¹` (component `μ`, weight `ŵ`), and weight numerator `j` (`ŵ = j 2^{-B}`). -/
structure MixCode (T : ℕ) where
  /-- The precision `B`. -/
  prec : ℕ
  /-- The numerators of `ν̂`. -/
  k0 : Fin T → ℕ
  /-- The numerators of `μ̂`. -/
  k1 : Fin T → ℕ
  /-- The numerator of `ŵ`. -/
  j : ℕ

/-- The cells `[B, k_1, …, k_T]` of a product code. -/
def encProd {T : ℕ} (c : ProdCode T) : List ℕ := c.prec :: List.ofFn c.k

/-- The cells `[B, k⁰_1, …, k⁰_T, k¹_1, …, k¹_T, j]` of a mixture code. -/
def encMix {T : ℕ} (c : MixCode T) : List ℕ := c.prec :: (List.ofFn c.k0 ++ List.ofFn c.k1 ++ [c.j])

/-- The cells of a list of mixture codes: their encodings, concatenated (each has `2T + 2` cells). -/
def encMixList {T : ℕ} (L : List (MixCode T)) : List ℕ := L.flatMap encMix

/-- The mean vector `k 2^{-B}`. -/
def dyadicVec {T : ℕ} (B : ℕ) (k : Fin T → ℕ) : Fin T → ℝ := fun i => (k i : ℝ) / 2 ^ B

/-- The law `Q_{k 2^{-B}}` of a product code. -/
def prodOfCode {T : ℕ} (c : ProdCode T) : Cube T → ℝ := prodLaw (dyadicVec c.prec c.k)

/-- The law `(1 − ŵ) Q_ν̂ + ŵ Q_μ̂` of a mixture code. -/
def mixOfCode {T : ℕ} (c : MixCode T) : Cube T → ℝ :=
  mixLaw ((c.j : ℝ) / 2 ^ c.prec) (dyadicVec c.prec c.k0) (dyadicVec c.prec c.k1)

/-- A proper dyadic balanced product (Appendix B.1): `B ≥ 1`, means in `[α, 1 − α]`. -/
def IsProperProdCode {T : ℕ} (α : ℝ) (c : ProdCode T) : Prop :=
  1 ≤ c.prec ∧ InBox α (dyadicVec c.prec c.k)

/-- A proper dyadic balanced two-mixture (Appendix B.1): `B ≥ 1`, both mean vectors in
`[α, 1 − α]^T`, `j ∈ {0, …, 2^B}`. Its law lies in `M_{2,α,T}`. -/
def IsProperMixCode {T : ℕ} (α : ℝ) (c : MixCode T) : Prop :=
  1 ≤ c.prec ∧ c.j ≤ 2 ^ c.prec ∧ InBox α (dyadicVec c.prec c.k0) ∧ InBox α (dyadicVec c.prec c.k1)

/-- The largest bit length `max_{i,x} (bits num + bits den)` of the candidate densities
`M_{i+1}(x)` (the encoding length of one density evaluation). -/
def densBits {T N : ℕ} (Ms : Fin N → Cube T → ℚ) : ℕ :=
  Finset.univ.sup fun p : Fin N × Cube T => bits (Ms p.1 p.2).num.toNat + bits (Ms p.1 p.2).den

/-- The learner's input `[T, α, θ, ε, δ]` (rationals as numerator/denominator pairs). -/
def learnerInput (T : ℕ) (α θ ε δ : ℚ) : List ℕ :=
  T :: (ratCells α ++ ratCells θ ++ ratCells ε ++ ratCells δ)

/-- The product learner's input `[T, α, ε, δ]`. -/
def productInput (T : ℕ) (α ε δ : ℚ) : List ℕ := T :: (ratCells α ++ ratCells ε ++ ratCells δ)

/-- The candidate generator's input `[T, α, ζ, δ]`. -/
def generatorInput (T : ℕ) (α ζ δ : ℚ) : List ℕ := T :: (ratCells α ++ ratCells ζ ++ ratCells δ)

/-- The comparison test's input `[d, ξ, x]`. -/
def testInput {d : ℕ} (ξ : ℚ) (x : Cube d) : List ℕ := d :: (ratCells ξ ++ cubeCells x)

/-- The selector's input `[T, ρ, δ, N]` (the candidates are reached through `selectorOracle`). -/
def selectorInput (T : ℕ) (ρ δ : ℚ) (N : ℕ) : List ℕ :=
  T :: (ratCells ρ ++ ratCells δ ++ [N])

end PrefixMixLearn.Proper



-- Prove2me | Definitions.Def_SubmodMDP_Policies_Machine
-- name    : SubmodMDP_Policies_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:42.495196+00:00
-- url     : https://prove2.me/theorems/1dba67ac-20e2-4b4e-9392-5fa22c6a8fcc
-- title:
--   The randomized value-oracle integer RAM with word-charged costs
-- statement:
--   This file fixes the model of computation in which every running time of the mission is measured. The paper (footnote 2) counts operations of a word RAM whose words can store every input value and every value returned by the submodular function $f$; it fixes nothing else, so the model is written out here.
--
--   **Machine.** A program is a finite list of instructions acting on integer registers $R[0],R[1],\dots$. On input $(z_1,\dots,z_L)$ the machine starts with $R[0]=L$, $R[i]=z_i$, all other registers $0$, and the program counter at $0$. The instructions are: load a literal, copy, $+$, $-$, $\times$, floor division and floor modulus (division by $0$ gives $0$), indirect load and store (negative addresses are read as $0$), unconditional and conditional jumps, halt, and two special instructions:
--
--   1. **query**: given a list of element indices in memory, write the numerator and the denominator (in lowest terms) of $f(X)$ for the set $X$ of listed ground elements;
--   2. **rand**: write a uniform random integer in $\{0,\dots,M-1\}$, where $M$ is the value of a register ($0$ if $M\le 0$).
--
--   When the machine halts, its output is $(R[1],\dots,R[R[0]])$.
--
--   **Cost.** Let $w$ be the word length: the maximum of $\lceil\log_2(L+2)\rceil$, the bit length of every input integer, and the bit length of the numerator and the denominator of every value $f(X)$. An instruction whose integer operands and results occupy at most $k$ words of $w$ bits costs $(1+k)^2$; a query on a list of $m$ indices costs $(1+m)(1+k)^2$; a jump costs $1$. Each instruction can therefore be simulated on a $w$-bit word RAM in $O(\text{cost})$ operations.
--
--   **Runs and laws.** A run is determined by the input, the oracle and the outcomes of the rand instructions, which are independent and uniform. The law of the final state (or of the output) within a fuel of $B$ steps is a finitely supported probability distribution; a program *halts within $B$* if every run halts with total cost at most $B$. A program without rand instructions is *deterministic*.
--
--   The file also fixes the encoding of rationals as pairs $[\text{num},\text{den}]$, their bit size, expectations over finitely supported laws, and a parser for the output formats.
--
--   **Formalization Note** The oracle has ground set $\{0,\dots,\texttt{size}-1\}$; query indices outside this range are ignored. Unit-cost arithmetic on unbounded integers is deliberately excluded: it would make the dependence of the running time on the encoding length meaningless.
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), footnote 2, p. 1 (PDF p. 2)

import Mathlib

namespace SubmodMDP.Policies

noncomputable section

open Classical

/-! # The randomized value-oracle integer RAM with word-charged costs

Footnote 2 of Rohwedder–Zenklusen (STOC 2027 submission #658, PDF p. 2) states running times
as the number of word-RAM operations, with words large enough to store every input value and
every value returned by the oracle `f`. This file fixes that model concretely.

* Memory: integer registers `R[0], R[1], …` (indexed by `ℕ`), all `0` initially except the
  input. Input `[z₁, …, z_L]` is stored as `R[0] = L`, `R[i] = zᵢ`.
* Output: when the machine halts, the output is `[R[1], …, R[R[0]]]` (`R[0]` read as a natural
  number, negative values as `0`).
* Instructions: `const`, `copy`, `+`, `-`, `×`, floor division, floor modulus (division and
  modulus by `0` give `0`), indirect load/store (negative addresses read as `0`), jumps,
  `query` (value oracle) and `rand` (uniform integer below a register value).
* Cost: an instruction whose integer operands and results have at most `k` words of `w` bits
  costs `(1 + k)²`; a `query` on a list of `m` element indices costs `(1 + m)·(1 + k)²`.
  `w` is the word length of `wordLen`: at least `⌈log₂(L+2)⌉`, the bit length of every input
  integer, and the bit length of the numerator and denominator of every oracle value. Each
  instruction is simulable on a `w`-bit word RAM in `O(cost)` operations.
-/

/-- Bit length of an integer: the number of binary digits of `|z|` (`bitLen 0 = 0`). -/
def bitLen (z : ℤ) : ℕ := Nat.size z.natAbs

/-- Number of `w`-bit words needed for `z`: `⌈bitLen z / w⌉`. -/
def words (w : ℕ) (z : ℤ) : ℕ := (bitLen z + w - 1) / w

/-- The instructions of the machine. Register arguments are register indices (natural numbers);
`target` is a program position. -/
inductive Instr where
  /-- stop. -/
  | halt
  /-- `R[dst] := k` for a literal `k` of the program. -/
  | const (dst : ℕ) (k : ℤ)
  /-- `R[dst] := R[src]`. -/
  | copy (dst src : ℕ)
  /-- `R[dst] := R[a] + R[b]`. -/
  | add (dst a b : ℕ)
  /-- `R[dst] := R[a] - R[b]`. -/
  | sub (dst a b : ℕ)
  /-- `R[dst] := R[a] * R[b]`. -/
  | mul (dst a b : ℕ)
  /-- `R[dst] := ⌊R[a] / R[b]⌋` (`0` if `R[b] = 0`). -/
  | div (dst a b : ℕ)
  /-- `R[dst] := R[a] mod R[b]` (floor convention; `R[a]` if `R[b] = 0`). -/
  | mod (dst a b : ℕ)
  /-- indirect load `R[dst] := R[R[addr]]`. -/
  | load (dst addr : ℕ)
  /-- indirect store `R[R[addr]] := R[src]`. -/
  | store (addr src : ℕ)
  /-- unconditional jump. -/
  | jmp (target : ℕ)
  /-- jump if `R[a] = 0`. -/
  | jz (a target : ℕ)
  /-- jump if `R[a] < R[b]`. -/
  | jlt (a b target : ℕ)
  /-- value-oracle query on the set of element indices `R[R[start]], …, R[R[start] + R[cnt] - 1]`;
  writes the reduced numerator of the value to `R[dnum]` and its denominator to `R[dden]`. -/
  | query (start cnt dnum dden : ℕ)
  /-- `R[dst] :=` a uniform random integer in `{0, …, M-1}` where `M = R[src]`; if `M ≤ 0`
  then `R[dst] := 0`. -/
  | rand (dst src : ℕ)

/-- A program is a finite list of instructions; execution starts at position `0`, and a
position outside the list halts. -/
abbrev Program := List Instr

/-- A program without `rand` instructions. -/
def Program.Deterministic (P : Program) : Prop :=
  ∀ i ∈ P, ∀ d s : ℕ, i ≠ Instr.rand d s

/-- A value oracle on the ground set `{0, …, size - 1}` with non-negative rational values. -/
structure Oracle where
  size : ℕ
  val : Finset (Fin size) → ℚ

/-- A machine state: program counter, memory, and accumulated cost. -/
structure State where
  pc : ℕ
  mem : ℕ → ℤ
  cost : ℕ

/-- Memory update. -/
def upd (m : ℕ → ℤ) (i : ℕ) (v : ℤ) : ℕ → ℤ := Function.update m i v

/-- Cost of one instruction touching the integers `vals`, repeated `mult` times:
`mult · (1 + k)²`, `k` the largest word count among `vals`. -/
def instrCost (w : ℕ) (vals : List ℤ) (mult : ℕ := 1) : ℕ :=
  mult * (1 + (vals.map (words w)).foldr max 0) ^ 2

/-- The element indices read by a query: `R[R[start] + i]` for `i < R[cnt]`. -/
def queryList (m : ℕ → ℤ) (start cnt : ℕ) : List ℤ :=
  (List.range (m cnt).toNat).map (fun i => m ((m start).toNat + i))

/-- The queried set: the ground elements whose index occurs in the query list (indices outside
`{0, …, size-1}` are ignored). -/
def querySet (O : Oracle) (m : ℕ → ℤ) (start cnt : ℕ) : Finset (Fin O.size) :=
  Finset.univ.filter (fun e => ((e : ℕ) : ℤ) ∈ queryList m start cnt)

/-- One step of a non-`rand`, non-`halt` instruction. -/
def stepDet (O : Oracle) (w : ℕ) (s : State) : Instr → State
  | .halt => s
  | .const d k => ⟨s.pc + 1, upd s.mem d k, s.cost + instrCost w [k]⟩
  | .copy d a => ⟨s.pc + 1, upd s.mem d (s.mem a), s.cost + instrCost w [s.mem a]⟩
  | .add d a b =>
      ⟨s.pc + 1, upd s.mem d (s.mem a + s.mem b),
        s.cost + instrCost w [s.mem a, s.mem b, s.mem a + s.mem b]⟩
  | .sub d a b =>
      ⟨s.pc + 1, upd s.mem d (s.mem a - s.mem b),
        s.cost + instrCost w [s.mem a, s.mem b, s.mem a - s.mem b]⟩
  | .mul d a b =>
      ⟨s.pc + 1, upd s.mem d (s.mem a * s.mem b),
        s.cost + instrCost w [s.mem a, s.mem b, s.mem a * s.mem b]⟩
  | .div d a b =>
      ⟨s.pc + 1, upd s.mem d (Int.fdiv (s.mem a) (s.mem b)),
        s.cost + instrCost w [s.mem a, s.mem b, Int.fdiv (s.mem a) (s.mem b)]⟩
  | .mod d a b =>
      ⟨s.pc + 1, upd s.mem d (Int.fmod (s.mem a) (s.mem b)),
        s.cost + instrCost w [s.mem a, s.mem b, Int.fmod (s.mem a) (s.mem b)]⟩
  | .load d a =>
      ⟨s.pc + 1, upd s.mem d (s.mem (s.mem a).toNat),
        s.cost + instrCost w [s.mem a, s.mem (s.mem a).toNat]⟩
  | .store a src =>
      ⟨s.pc + 1, upd s.mem (s.mem a).toNat (s.mem src),
        s.cost + instrCost w [s.mem a, s.mem src]⟩
  | .jmp t => ⟨t, s.mem, s.cost + 1⟩
  | .jz a t => ⟨if s.mem a = 0 then t else s.pc + 1, s.mem, s.cost + instrCost w [s.mem a]⟩
  | .jlt a b t =>
      ⟨if s.mem a < s.mem b then t else s.pc + 1, s.mem,
        s.cost + instrCost w [s.mem a, s.mem b]⟩
  | .query st c dn dd =>
      let v := O.val (querySet O s.mem st c)
      ⟨s.pc + 1, upd (upd s.mem dn v.num) dd (v.den : ℤ),
        s.cost + instrCost w ([s.mem st, s.mem c, v.num, (v.den : ℤ)] ++ queryList s.mem st c)
          (1 + (s.mem c).toNat)⟩
  | .rand _ _ => s

/-- The state is halted: the program counter is outside the program or at a `halt`. -/
def isHalted (P : Program) (s : State) : Bool :=
  match P[s.pc]? with
  | none => true
  | some .halt => true
  | some _ => false

/-- Execution for at most `fuel` steps, as the exact law of the final state over the
independent uniform outcomes of the `rand` instructions; `none` if the run has not halted after
`fuel` steps. -/
def exec (P : Program) (O : Oracle) (w : ℕ) : ℕ → State → PMF (Option State)
  | 0, s => if isHalted P s then PMF.pure (some s) else PMF.pure none
  | fuel + 1, s =>
    match P[s.pc]? with
    | none => PMF.pure (some s)
    | some .halt => PMF.pure (some s)
    | some (.rand d src) =>
        if h : 1 ≤ s.mem src then
          (PMF.uniformOfFinset (Finset.range (s.mem src).toNat)
              ⟨0, Finset.mem_range.mpr (by omega)⟩).bind
            (fun k => exec P O w fuel
              ⟨s.pc + 1, upd s.mem d (k : ℤ), s.cost + instrCost w [s.mem src, (k : ℤ)]⟩)
        else
          exec P O w fuel ⟨s.pc + 1, upd s.mem d 0, s.cost + instrCost w [s.mem src]⟩
    | some i => exec P O w fuel (stepDet O w s i)

/-- The initial state on input `inp`: `R[0] = inp.length`, `R[i] = inp[i-1]`. -/
def initState (inp : List ℤ) : State :=
  ⟨0, fun i => if i = 0 then (inp.length : ℤ) else inp.getD (i - 1) 0, 0⟩

/-- The output of a halted state: `[R[1], …, R[R[0]]]`. -/
def State.output (s : State) : List ℤ :=
  (List.range (s.mem 0).toNat).map (fun i => s.mem (i + 1))

/-- The word length `w` of a run on input `inp` with oracle `O` (footnote 2): the maximum of
`⌈log₂ (inp.length + 2)⌉`, the bit lengths of all input integers, and the bit lengths of the
numerator and denominator of every oracle value. -/
def wordLen (inp : List ℤ) (O : Oracle) : ℕ :=
  max (Nat.clog 2 (inp.length + 2))
    (max ((inp.map bitLen).foldr max 0)
      ((Finset.univ : Finset (Finset (Fin O.size))).sup
        (fun X => max (bitLen (O.val X).num) (bitLen ((O.val X).den : ℤ)))))

/-- Every run of `P` on `inp` (for every sequence of `rand` outcomes) halts with total cost at
most `B`. (Each executed instruction costs at least `1`, so `B` steps of fuel suffice.) -/
def HaltsWithin (P : Program) (O : Oracle) (w : ℕ) (inp : List ℤ) (B : ℕ) : Prop :=
  ∀ o ∈ (exec P O w B (initState inp)).support, ∃ s : State, o = some s ∧ s.cost ≤ B

/-- The output law of `P` on `inp` within fuel `B` (`none` = not halted). -/
def outLaw (P : Program) (O : Oracle) (w : ℕ) (inp : List ℤ) (B : ℕ) : PMF (Option (List ℤ)) :=
  (exec P O w B (initState inp)).map (Option.map State.output)

/-- `P` halts on `inp` within cost `B` and outputs `out` with probability one. -/
def Computes (P : Program) (O : Oracle) (w : ℕ) (inp : List ℤ) (B : ℕ) (out : List ℤ) : Prop :=
  HaltsWithin P O w inp B ∧ outLaw P O w inp B = PMF.pure (some out)

/-- The output of a run that is certain (used for deterministic programs); `none` otherwise. -/
def detOutput (P : Program) (O : Oracle) (w : ℕ) (inp : List ℤ) (B : ℕ) : Option (List ℤ) :=
  if h : ∃ out, outLaw P O w inp B = PMF.pure (some out) then some h.choose else none

/-! ## Probabilities and expectations over finite laws -/

/-- Expectation of a real function under a PMF (all laws in this mission have finite support). -/
def pmfExp {α : Type} (μ : PMF α) (g : α → ℝ) : ℝ := ∑' a, (μ a).toReal * g a

/-! ## Encodings of rationals and a small parser for outputs -/

/-- A rational as the two integers `[num, den]` (reduced, `den > 0`). -/
def encRat (q : ℚ) : List ℤ := [q.num, (q.den : ℤ)]

/-- Total bit length of a rational in lowest terms. -/
def ratBits (q : ℚ) : ℕ := bitLen q.num + bitLen (q.den : ℤ)

/-- Parsers of integer lists. -/
abbrev Parser (α : Type) := StateT (List ℤ) Option α

/-- Read one integer. -/
def pInt : Parser ℤ := fun l =>
  match l with
  | [] => none
  | z :: t => some (z, t)

/-- Read a rational `num / den` with `den > 0`. -/
def pRat : Parser ℚ := do
  let a ← pInt
  let b ← pInt
  if 0 < b then pure ((a : ℚ) / (b : ℚ)) else failure

/-- Read a natural number (a non-negative integer). -/
def pNat : Parser ℕ := do
  let z ← pInt
  if 0 ≤ z then pure z.toNat else failure

/-- Read an element of `Fin N` (an integer in `{0, …, N-1}`). -/
def pFin (N : ℕ) : Parser (Fin N) := do
  let z ← pInt
  if h : 0 ≤ z ∧ z.toNat < N then pure ⟨z.toNat, h.2⟩ else failure

/-- Run a parser on the whole list; fails unless the whole list is consumed. -/
def parseAll {α : Type} (p : Parser α) (l : List ℤ) : Option α :=
  match p.run l with
  | some (a, []) => some a
  | _ => none

/-- The function given by a table of pairs (first match), `dflt` elsewhere. -/
def tableFn {β γ : Type} [DecidableEq β] (L : List (β × γ)) (dflt : γ) (b : β) : γ :=
  ((L.find? (fun p => decide (p.1 = b))).map Prod.snd).getD dflt

end

end SubmodMDP.Policies



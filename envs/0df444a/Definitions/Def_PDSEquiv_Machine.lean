-- Prove2me | Definitions.Def_PDSEquiv_Machine
-- name    : PDSEquiv_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:40.971202+00:00
-- url     : https://prove2.me/theorems/2e5021db-b1db-4ff0-891a-08f42d9ead7f
-- title:
--   The randomized log-cost oracle RAM: programs, runs, output mass, time and query bounds, typed oracles
-- statement:
--   The paper charges "unit cost for an independent $\mathrm{Ber}(\theta)$ draw when $\theta$ is rational with $O(\log N)$-bit numerator and denominator", lets oracle calls use fresh randomness, and counts "the algorithm's own computation, including query preparation and answer processing" plus one step per oracle call (§4.1). It names no machine; this definition fixes one.
--
--   1. **Programs.** A program is a finite list of instructions over natural-number registers and memory: constants, copy, $+$, truncated $-$, $\times$, division, remainder, bitwise xor/and, shifts, load, store, two conditional jumps, $\mathrm{ber}\,d\,a\,b$ (write $1$ with probability $a/b$ and $0$ otherwise, exactly, when $0<b$ and $a\le b$), $\mathrm{query}$ (send a block of memory cells to the oracle and write the reply back) and $\mathrm{halt}$ (output a block of cells).
--   2. **Cost.** Every instruction costs one plus the bit lengths of every address, operand and result it touches, as in a log-cost RAM. A query is charged for the cells it reads and the reply it writes. A second counter records the number of executed instructions. A halted machine stays put at no cost; a program counter outside the program keeps being charged.
--   3. **Semantics.** With an oracle (a map from a query to a law of replies), a program defines a law of the machine state after $t$ steps; the probability of output $\ell$ is the limit in $t$ of the mass of "halted with output $\ell$".
--   4. **Bounds.** `HaltsWithin` $B$ $B_q$ means: on every random branch at every time, cost $\le B$, at most $B_q$ queries, and halted by time $B$. A **polynomial-time algorithm** makes no query and halts within $(N+2)^c$ on every graph on $[N]$, for every $N$.
--   5. **Encodings.** A graph is input as $N$ followed by its edge bits in lexicographic pair order, so a program reads $N$ from its input. A set $T\subseteq[N]$ is output as its $N$-bit characteristic list; the output $[1]$ is acceptance (value $1$), every other output the value $-1$.
--   6. **Typed oracles.** A randomized distinguisher, or search algorithm, on graphs of every size, possibly also receiving an integer $k$, is turned into an oracle answering a well-formed query with $[1]$ or $[0]$, or with the characteristic list of its output set, and $[\,]$ otherwise.
--
--   **Formalization Note** The instruction set and charging follow the published `Z2PostSamp.Machine`, with `ber` in place of fair coins (Lemma 6.5(i) is an exact inequality and needs exact $\mathrm{Ber}(q)$ draws) and an oracle instruction. Polynomial time on this machine is polynomial time on a Turing machine. Any rational $\theta$ is allowed, charged by its bit lengths.
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), §4.1, pp.12–13 (Algorithms; oracle access and charging)

import Mathlib
import Definitions.Def_PDSEquiv_Laws

set_option autoImplicit false

open scoped ENNReal

namespace PDSEquiv

noncomputable section

/-!
# The randomized log-cost oracle RAM

S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), §4.1, pp.12–13: "An algorithm receives the graph and any additional
inputs explicitly specified in the statement"; "it reads N from the graph"; "We charge unit cost for
an independent Ber(θ) draw when θ is rational with O(log N)-bit numerator and denominator"; "Each
oracle call uses fresh randomness"; "We count the algorithm's own computation, including query
preparation and answer processing, and charge one additional step per oracle call."

**Formalization Note.** The paper names no machine. This is a log-cost RAM with natural-number
words, patterned on the published `Z2PostSamp.Machine` (same arithmetic, bitwise and jump
instructions and the same charging: one plus the bit lengths of every address, operand and result).
Three things differ. (a) `ber` replaces the fair coin: it draws `Ber(a/b)` exactly, because
Lemma 6.5(i) is an exact inequality needing exact `Ber(q)` draws, which fair coins cannot give in
bounded time; it is charged by bit lengths, a polynomial factor over the page's unit cost, and any
rational `θ` is allowed. (b) `query` calls an oracle with fresh randomness per call; it reads a list
of cells, and its reply is written to cells, both charged cell by cell. (c) There are registers
(`reg`, fixed addresses, the operands of every arithmetic instruction) and a separate memory (`mem`,
reached only through `load`, `store`, `query`, `halt`, holding the input from cell `0`), so a
program has scratch space on inputs of every length; this changes no complexity class. Two counters are kept: `cost` (log-cost,
polynomial time) and `steps` (executed instructions), the latter only for the explicit running time
of Lemma 5.5(iii). A halted machine stutters at no cost; a program counter outside the program is
stuck and keeps being charged, so a program cannot halt by running off its end.
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
  /-- `reg[d] := 1` with probability `reg[a]/reg[b]` and `0` otherwise, when `0 < reg[b]` and
  `reg[a] ≤ reg[b]`; `reg[d] := 0` otherwise. A fresh draw each time. -/
  | ber (d a b : ℕ)
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
  /-- The number of executed instructions. -/
  steps : ℕ
  /-- The log-cost time charged so far. -/
  cost : ℕ
  /-- The oracle queries made so far, oldest first. -/
  queries : List (List ℕ)
  /-- The output, once the machine has halted. -/
  out : Option (List ℕ)

/-- The input convention: the list of naturals in memory cells `0, 1, …`, everything else `0`. -/
def initState (input : List ℕ) : MState :=
  ⟨0, fun _ => 0, fun i => input.getD i 0, 0, 0, [], none⟩

/-- The bit length of a natural number, `Nat.size 0 = 0`. -/
abbrev bits (x : ℕ) : ℕ := Nat.size x

/-- An oracle: a query (a list of cells) and a fresh draw of a reply (a list of cells). -/
abbrev Oracle := List ℕ → PMF (List ℕ)

/-- Reads `l` consecutive memory cells from `a`. -/
def MState.readCells (s : MState) (a l : ℕ) : List ℕ :=
  (List.range l).map fun i => s.mem (a + i)

/-- The log-cost of reading `l` consecutive memory cells from `a`: per cell, one plus the bits of its
address and of its contents. -/
def MState.readCost (s : MState) (a l : ℕ) : ℕ :=
  ((List.range l).map fun i => 1 + bits (a + i) + bits (s.mem (a + i))).sum

/-- Advances the program counter and the two counters. -/
def MState.tick (s : MState) (c : ℕ) : MState :=
  { s with pc := s.pc + 1, steps := s.steps + 1, cost := s.cost + c }

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
    steps := s.steps + 1
    cost := s.cost + (1 + bits a + bits b + bits t + bits (s.reg a) + bits (s.reg b)) }

/-- `Ber(a/b)`, exactly, as a uniform draw from `Fin b`; `false` unless `0 < b` and `a ≤ b`. -/
def berLaw (a b : ℕ) : PMF Bool :=
  if h : 0 < b ∧ a ≤ b then
    haveI : Nonempty (Fin b) := ⟨⟨0, h.1⟩⟩
    (PMF.uniformOfFintype (Fin b)).map fun u => decide (u.val < a)
  else PMF.pure false

/-- Writes the oracle's reply `r` at `a`: its length, then its entries. -/
def writeReply (m : ℕ → ℕ) (a : ℕ) (r : List ℕ) : ℕ → ℕ :=
  fun i =>
    if i = a then r.length
    else if a < i ∧ i ≤ a + r.length then r.getD (i - a - 1) 0
    else m i

/-- One executed instruction. Only `ber` and `query` draw randomness. -/
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
  | .ber d a b =>
    (berLaw (s.reg a) (s.reg b)).map fun c =>
      s.setReg d (if c then 1 else 0)
        (2 + bits d + bits a + bits b + bits (s.reg a) + bits (s.reg b))
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
        steps := s.steps + 1
        cost := s.cost + (1 + bits a + bits l + bits (s.reg a) + bits (s.reg l)
            + s.readCost (s.reg a) (s.reg l)) }

/-- One machine step. A halted machine stutters at zero cost; a program counter outside the program
is stuck and keeps being charged. -/
def step (Q : Oracle) (P : Program) (s : MState) : PMF MState :=
  match s.out with
  | some _ => PMF.pure s
  | none =>
    match P[s.pc]? with
    | none => PMF.pure { s with steps := s.steps + 1, cost := s.cost + 1 }
    | some i => stepInstr Q i s

/-- The law of the machine state after `t` steps. -/
def runLaw (P : Program) (Q : Oracle) (input : List ℕ) : ℕ → PMF MState
  | 0 => PMF.pure (initState input)
  | t + 1 => (runLaw P Q input t).bind (step Q P)

/-- The probability that the machine halts with output `ℓ`, as a real. -/
def outMass (P : Program) (Q : Oracle) (input : List ℕ) (ℓ : List ℕ) : ℝ :=
  (⨆ t, (runLaw P Q input t).toOuterMeasure {s | s.out = some ℓ}).toReal

/-- The expectation of `f` of the output. -/
def outExpect (P : Program) (Q : Oracle) (input : List ℕ) (f : List ℕ → ℝ) : ℝ :=
  ∑' ℓ : List ℕ, outMass P Q input ℓ * f ℓ

/-- On every random branch, at every time: the log-cost is at most `B`, at most `Bq` queries have
been made, and the machine has halted by time `B`. -/
def HaltsWithin (P : Program) (Q : Oracle) (input : List ℕ) (B Bq : ℕ) : Prop :=
  ∀ t, ∀ s ∈ (runLaw P Q input t).support,
    s.cost ≤ B ∧ s.queries.length ≤ Bq ∧ (B ≤ t → s.out.isSome = true)

/-- On every random branch, every query made satisfies `form`. -/
def QueriesSatisfy (P : Program) (Q : Oracle) (input : List ℕ) (form : List ℕ → Prop) : Prop :=
  ∀ t, ∀ s ∈ (runLaw P Q input t).support, ∀ q ∈ s.queries, form q

/-- On every random branch, once halted, the output satisfies `form`. -/
def OutputsSatisfy (P : Program) (Q : Oracle) (input : List ℕ) (form : List ℕ → Prop) : Prop :=
  ∀ t, ∀ s ∈ (runLaw P Q input t).support, ∀ o, s.out = some o → form o

/-- On every random branch, once halted, exactly `n` queries have been made. -/
def QueryCountEq (P : Program) (Q : Oracle) (input : List ℕ) (n : ℕ) : Prop :=
  ∀ t, ∀ s ∈ (runLaw P Q input t).support, s.out.isSome = true → s.queries.length = n

/-- On every random branch, at every time, the executed instructions number at most `X` and the
queries at most `Y`. -/
def StepsQueriesWithin (P : Program) (Q : Oracle) (input : List ℕ) (X Y : ℝ) : Prop :=
  ∀ t, ∀ s ∈ (runLaw P Q input t).support, (s.steps : ℝ) ≤ X ∧ (s.queries.length : ℝ) ≤ Y

/-- The program calls no oracle. -/
def IsAlgorithm (P : Program) : Prop :=
  ∀ i ∈ P, ∀ d a l, i ≠ Instr.query d a l

/-- The oracle of an algorithm with no oracle access. -/
def noOracle : Oracle := fun _ => PMF.pure []

/-- All pairs of `[N]` in lexicographic order. -/
def pairList (N : ℕ) : List (Pair N) :=
  (List.finRange N).flatMap fun i =>
    (List.finRange N).filterMap fun j => if h : i < j then some ⟨(i, j), h⟩ else none

/-- The edge indicators of `G`, in the order of `pairList`. -/
def graphBits {N : ℕ} (G : Graph N) : List ℕ :=
  (pairList N).map fun e => if G e then 1 else 0

/-- The input encoding of a graph: `N`, then its edge indicators. The program reads `N` from it. -/
def enc {N : ℕ} (G : Graph N) : List ℕ := N :: graphBits G

/-- The output encoding of a subset of `[N]`: its `N`-bit characteristic list. -/
def charList {N : ℕ} (T : Finset (Fin N)) : List ℕ :=
  (List.finRange N).map fun i => if i ∈ T then 1 else 0

/-- The output encoding of a distinguisher's value: `[1]` is `1`, `[0]` is `−1`. -/
def valueList (b : Bool) : List ℕ := [if b then 1 else 0]

/-- The acceptance output. Every other output counts as the value `−1`. -/
def acceptOut : List ℕ := [1]

/-- A distinguisher's output: `[1]` or `[0]`. -/
def IsValueOut (o : List ℕ) : Prop := o = [1] ∨ o = [0]

/-- An output `[u, v]` read as the rational `u/v ∈ [0, 1]`. -/
def IsRatOut (o : List ℕ) : Prop := ∃ u v : ℕ, o = [u, v] ∧ 0 < v ∧ u ≤ v

/-- The value of an output `[u, v]`. -/
def ratOut : List ℕ → ℝ
  | [u, v] => (u : ℝ) / v
  | _ => 0

open Classical in
/-- The graph a query encodes, if any. -/
def decodeGraph (q : List ℕ) : Option (Σ m, Graph m) :=
  if h : ∃ x : Σ m, Graph m, enc x.2 = q then some h.choose else none

open Classical in
/-- The graph and the additional integer that a query `[m, k, bits…]` encodes, if any. -/
def decodeGraphK (q : List ℕ) : Option ((Σ m, Graph m) × ℕ) :=
  if h : ∃ x : (Σ m, Graph m) × ℕ, x.1.1 :: x.2 :: graphBits x.1.2 = q then some h.choose else none

/-- A randomized distinguisher, as a family of laws of its acceptance, one per graph of every size.
The value at `true` is the probability of the value `1`. -/
abbrev DistFamily := ∀ m, Graph m → PMF Bool

/-- A randomized search algorithm, as a family of laws of its output set. -/
abbrev SearchFamily := ∀ m, Graph m → PMF (Finset (Fin m))

/-- A distinguisher taking `(G, k)`, §8.1, p.33. -/
abbrev DistFamilyK := ∀ m, Graph m → ℕ → PMF Bool

/-- A search algorithm taking `(G, k)`, §8.1, p.33. -/
abbrev SearchFamilyK := ∀ m, Graph m → ℕ → PMF (Finset (Fin m))

/-- The oracle of a distinguisher: a query `enc G` gets `[1]` or `[0]`, a malformed one gets `[]`, so
replies are bounded and a bound holding for every oracle can hold. -/
def distOracle (d : DistFamily) : Oracle := fun q =>
  match decodeGraph q with
  | some ⟨m, G⟩ => (d m G).map valueList
  | none => PMF.pure []

/-- The oracle of a search algorithm: a query `enc G` gets the characteristic list of the set. -/
def searchOracle (s : SearchFamily) : Oracle := fun q =>
  match decodeGraph q with
  | some ⟨m, G⟩ => (s m G).map charList
  | none => PMF.pure []

/-- The oracle of a distinguisher taking `(G, k)`: the query is `[m, k, bits…]`. -/
def distOracleK (d : DistFamilyK) : Oracle := fun q =>
  match decodeGraphK q with
  | some (⟨m, G⟩, k) => (d m G k).map valueList
  | none => PMF.pure []

/-- The oracle of a search algorithm taking `(G, k)`: the query is `[m, k, bits…]`. -/
def searchOracleK (s : SearchFamilyK) : Oracle := fun q =>
  match decodeGraphK q with
  | some (⟨m, G⟩, k) => (s m G k).map charList
  | none => PMF.pure []

/-- A query that is an `m`-vertex graph. -/
def IsGraphQuery (m : ℕ) (q : List ℕ) : Prop := ∃ G : Graph m, q = enc G

/-- A query `(G, k)` with `G` a graph on `[N]` and `k ∈ [N]`, §8.1, p.33. -/
def IsGraphQueryK (N : ℕ) (q : List ℕ) : Prop :=
  ∃ (G : Graph N) (k : ℕ), 1 ≤ k ∧ k ≤ N ∧ q = N :: k :: graphBits G

/-- The probability that a distinguisher accepts `G`. -/
def distAcc (d : DistFamily) {m : ℕ} (G : Graph m) : ℝ := (d m G true).toReal

/-- The probability that a search algorithm outputs `C` on `G`. -/
def searchRec (s : SearchFamily) {m : ℕ} (G : Graph m) (C : Finset (Fin m)) : ℝ :=
  (s m G C).toReal

/-- A polynomial-time randomized algorithm: no oracle call, and on every branch, for every `N` and
every graph on `[N]`, it halts within log-cost `(N + 2) ^ c`. -/
def PolyTimeAlg (P : Program) : Prop :=
  IsAlgorithm P ∧ ∃ c : ℕ, ∀ (N : ℕ) (G : Graph N), HaltsWithin P noOracle (enc G) ((N + 2) ^ c) 0

end

end PDSEquiv



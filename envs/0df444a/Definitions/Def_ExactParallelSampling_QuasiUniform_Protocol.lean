-- Prove2me | Definitions.Def_ExactParallelSampling_QuasiUniform_Protocol
-- name    : ExactParallelSampling_QuasiUniform_Protocol
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:50:06.758196+00:00
-- url     : https://prove2.me/theorems/4e8abcde-d1a3-44ee-8c5e-1517de3908f4
-- title:
--   Adaptive randomized oracle algorithms in rounds: counting oracle and independence oracle with circuit recovery
-- statement:
--   The model of §2.1 (p. 12) and of §6 (p. 28). An algorithm is fixed before the unknown input and reaches it only through oracle answers.
--
--   - **Randomness.** A tape $\omega\in[0,1]^{\mathbb N}$ of independent uniform numbers (`tapeLaw`, the infinite product of Lebesgue measure). Between rounds the algorithm computes exactly and can sample from any distribution it has computed.
--   - **Protocol.** `Protocol Q A O` has a map `next` from the transcript so far (the earlier batches with the answers to exactly those queries) and the tape to an action: halt with an output, or submit a finite batch of queries (one round). For each transcript, `next` is a measurable function of the tape.
--   - **Runs.** Against an oracle `ans : Q → A`, `transcript` is the sequence of transcripts, `rounds` the first step at which it halts ($\top$ if never), `output` the output (`none` if it never halts), `batchAt r` the batch of step $r$, and `Queried q` says that $q$ was asked in some round.
--   - **Counting oracle on $[q]^n$.** Queries are pairs $(S,y)$; `countOracle p` answers $\Pr[X_S=y_S]$. A `CountAlgorithm` gives a protocol for every $n,q$ (which it knows). `SamplesExactly P p`: it halts with probability $1$ and $\Pr[\text{output}=x]=p(x)$ for every $x$. `expectedRounds` is $\mathbb E[T]$ as a non-negative extended real.
--   - **Independence oracle with circuit recovery (§6).** Queries are `indep T` ("is $T\in I$?") and `recover B x` (an instance of $\mathrm{Rec}$). `indepOracle I recAns` answers them; `IsCircuitRecovery I recAns` says $\mathrm{Rec}$ returns exactly the family of all circuits contained in $B+x$ whenever $B\in I$, $x\notin B$, $B+x\notin I$ (assumption (A2)); elsewhere its answer is arbitrary. One step costs $1$ round if it asks independence queries and $\rho$ rounds if it runs $\mathrm{Rec}$ instances (the larger if both); `iterRounds` sums these costs up to halting. `numIndep`, `numRec` count the queries of each kind in a batch. Outputs of an iteration are "contract $U$", "defer $R$ with certificates $T_x$", or "fail" (`IterOutput`). An `IterAlgorithm` gives a protocol for every ground-set size $m$ and every $\rho$.
--
--   `transcriptAnswer` reads only an answer stored in a completed round. `RecoveryCallsValid` requires every issued recovery input to satisfy (A2); this is a conclusion in Theorem 6.1. The charged-round function `iterRounds` also applies to protocols returning a set, as GreedyOpt does.
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, §2.1 and §6 (assumptions (A1), (A2)), p. 12, 28; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_Distributions

noncomputable section
open Classical MeasureTheory

namespace ExactParallelSampling.QuasiUniform

/-! # Adaptive randomized algorithms that query an oracle in rounds (§2.1, p. 12; §6, p. 28)

An algorithm is fixed before the unknown input. Its only access to the input is through oracle
answers. It runs in rounds: in each round it submits a finite batch of queries that is a function
of the answers of earlier rounds and of its private random bits, or it halts with an output.
Computation between rounds is free and exact. The private randomness is a tape of independent
uniform `[0, 1]` numbers, so the algorithm can sample exactly from any distribution it has
computed. A run may never halt; halting is a conclusion of the theorems, not part of the model. -/

/-- The random tape: an infinite sequence of reals in `[0, 1]`. -/
abbrev Tape := ℕ → unitInterval

/-- Its law: independent uniform coordinates (the infinite product of Lebesgue measure on
`[0, 1]`). -/
def tapeLaw : Measure Tape :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

/-- What the algorithm does next: halt with an output, or submit a batch of queries (one round). -/
inductive Action (Q O : Type) where
  | halt (o : O)
  | ask (batch : Finset Q)

/-- One completed round of the transcript: the batch and the oracle's answers to exactly those
queries. -/
abbrev RoundRecord (Q A : Type) := Σ b : Finset Q, (↥b → A)

/-- A transcript: the completed rounds in order. -/
abbrev Transcript (Q A : Type) := List (RoundRecord Q A)

/-- An adaptive randomized oracle algorithm. Its next action is a function of the transcript so far
(earlier batches and their answers) and of its random tape only; it cannot read the input in any
other way. For each transcript the action is a measurable function of the tape. -/
structure Protocol (Q A O : Type) where
  next : Transcript Q A → Tape → Action Q O
  measurable_next : ∀ (h : Transcript Q A) (a : Action Q O), MeasurableSet {ω | next h ω = a}

namespace Protocol

variable {Q A O : Type}

/-- The transcript after `r` steps of a run against the oracle `ans` with tape `ω` (it stops
growing once the algorithm halts). -/
def transcript (P : Protocol Q A O) (ans : Q → A) (ω : Tape) : ℕ → Transcript Q A
  | 0 => []
  | r + 1 =>
    match P.next (transcript P ans ω r) ω with
    | .halt _ => transcript P ans ω r
    | .ask b => transcript P ans ω r ++ [⟨b, fun q => ans q.1⟩]

/-- The action taken at step `r`. -/
def actionAt (P : Protocol Q A O) (ans : Q → A) (ω : Tape) (r : ℕ) : Action Q O :=
  P.next (P.transcript ans ω r) ω

/-- Whether an action is `halt`. -/
def Action.IsHalt {Q O : Type} : Action Q O → Prop
  | .halt _ => True
  | .ask _ => False

/-- The number of rounds of the run: the first step at which the algorithm halts (`⊤` if it never
halts). Every earlier step submitted one batch, i.e. used one round. -/
def rounds (P : Protocol Q A O) (ans : Q → A) (ω : Tape) : ℕ∞ :=
  if h : ∃ r, Action.IsHalt (P.actionAt ans ω r) then (Nat.find h : ℕ∞) else ⊤

/-- The output of the run (`none` if it never halts). -/
def output (P : Protocol Q A O) (ans : Q → A) (ω : Tape) : Option O :=
  if h : ∃ r, Action.IsHalt (P.actionAt ans ω r) then
    match P.actionAt ans ω (Nat.find h) with
    | .halt o => some o
    | .ask _ => none
  else none

/-- The batch submitted at step `r` (empty if the action at step `r` is `halt`). -/
def batchAt (P : Protocol Q A O) (ans : Q → A) (ω : Tape) (r : ℕ) : Finset Q :=
  match P.actionAt ans ω r with
  | .halt _ => ∅
  | .ask b => b

/-- `q` was queried in some round of the run. -/
def Queried (P : Protocol Q A O) (ans : Q → A) (ω : Tape) (q : Q) : Prop :=
  ∃ r : ℕ, (r : ℕ∞) < P.rounds ans ω ∧ q ∈ P.batchAt ans ω r

end Protocol

/-! ## The counting oracle of a distribution on `[q]^n` -/

/-- A counting query `(S, y)`: a set of coordinates and a pinning (only `y` on `S` matters). -/
abbrev CountQuery (n q : ℕ) := Finset (Fin n) × (Fin n → Fin q)

/-- The counting oracle of `μ` on `[q]^n`: `(S, y) ↦ Pr[X_S = y_S]`, an exact real number. -/
def countOracle {n q : ℕ} (p : (Fin n → Fin q) → ℝ) : CountQuery n q → ℝ :=
  fun Q => count p Q.1 Q.2

/-- A counting-oracle sampling algorithm: for every `n` and `q` (which it is given), a protocol
whose queries are counting queries, whose answers are reals and whose output is a point of
`[q]^n`. One algorithm is fixed before the unknown distribution. -/
abbrev CountAlgorithm := (n q : ℕ) → Protocol (CountQuery n q) ℝ (Fin n → Fin q)

/-- The algorithm samples `μ` exactly (§2.1): it halts with probability `1` and its output is
distributed according to `μ`. -/
def SamplesExactly {n q : ℕ} (P : Protocol (CountQuery n q) ℝ (Fin n → Fin q))
    (p : (Fin n → Fin q) → ℝ) : Prop :=
  tapeLaw {ω | P.rounds (countOracle p) ω = ⊤} = 0 ∧
    ∀ x, tapeLaw {ω | P.output (countOracle p) ω = some x} = ENNReal.ofReal (p x)

/-- The expected number of rounds `E[T]` (a non-negative extended real; `T = ⊤` on runs that never
halt). -/
def expectedRounds {n q : ℕ} (P : Protocol (CountQuery n q) ℝ (Fin n → Fin q))
    (p : (Fin n → Fin q) → ℝ) : ENNReal :=
  ∫⁻ ω, ((P.rounds (countOracle p) ω : ℕ∞) : ENNReal) ∂tapeLaw

/-! ## The independence oracle with a circuit-recovery procedure (§6, p. 28)

An algorithm on an independence system `I` over the ground set `Fin m` asks independence queries
`T ∈ I?` and may run instances `(B, x)` of a circuit-recovery procedure `Rec` (assumption (A2)),
which returns the family of all circuits contained in `B + x` when `B ∈ I`, `x ∉ B`, `B + x ∉ I`
and takes `ρ` rounds of queries to a richer oracle, counted separately. A round that runs `Rec`
instances therefore costs `ρ` rounds. On inputs outside (A2) the answer of `Rec` is arbitrary. -/

/-- A query to the independence oracle, or an instance of `Rec`. -/
inductive IQuery (E : Type) where
  | indep (T : Finset E)
  | recover (B : Finset E) (x : E)

/-- An answer: a truth value for an independence query, a family of sets for `Rec`. -/
inductive IAnswer (E : Type) where
  | bool (b : Bool)
  | family (F : Finset (Finset E))

/-- The output of one iteration (Theorem 6.1): contract `U`, defer `R` with certificates `T_x`,
or fail. -/
inductive IterOutput (E : Type) where
  | contract (U : Finset E)
  | defer (R : Finset E) (cert : E → Finset E)
  | fail

/-- The oracle answering independence queries by `I` and `Rec` instances by `recAns`. -/
def indepOracle {E : Type} (I : Finset E → Prop) (recAns : Finset E → E → Finset (Finset E)) :
    IQuery E → IAnswer E
  | .indep T => .bool (decide (I T))
  | .recover B x => .family (recAns B x)

/-- `recAns` is a correct circuit recovery for `I` in the sense of (A2): on every `B ∈ I`, `x ∉ B`
with `B + x ∉ I` it returns the family of all circuits contained in `B + x`. -/
def IsCircuitRecovery {E : Type} [Fintype E] (I : Finset E → Prop)
    (recAns : Finset E → E → Finset (Finset E)) : Prop :=
  ∀ B x, I B → x ∉ B → ¬ I (insert x B) → recAns B x = circuitsIn I (insert x B)

/-- Number of independence queries in a batch. -/
def numIndep {E : Type} (b : Finset (IQuery E)) : ℕ :=
  (b.filter (fun q => ∃ T, q = .indep T)).card

/-- Number of `Rec` instances in a batch. -/
def numRec {E : Type} (b : Finset (IQuery E)) : ℕ :=
  (b.filter (fun q => ∃ B x, q = .recover B x)).card

/-- Rounds used by one step: `1` if it asks independence queries, `ρ` if it runs `Rec` instances
(the larger of the two if it does both). -/
def stepCost {E : Type} (ρ : ℕ) (b : Finset (IQuery E)) : ℕ :=
  max (if 0 < numIndep b then 1 else 0) (if 0 < numRec b then ρ else 0)

/-- An iteration algorithm on ground sets `Fin m`: for every `m` and `ρ` (which it is given), a
protocol in the independence-oracle model with output in `IterOutput (Fin m)`. -/
abbrev IterAlgorithm :=
  (m ρ : ℕ) → Protocol (IQuery (Fin m)) (IAnswer (Fin m)) (IterOutput (Fin m))

/-- The number of rounds of a run of an independence-oracle protocol: the sum of the step costs up
to halting (`⊤` if it never halts). -/
def iterRounds {E O : Type} (P : Protocol (IQuery E) (IAnswer E) O)
    (ρ : ℕ) (ans : IQuery E → IAnswer E) (ω : Tape) : ℕ∞ :=
  if h : ∃ r, Protocol.Action.IsHalt (P.actionAt ans ω r) then
    ((∑ r ∈ Finset.range (Nat.find h), stepCost ρ (P.batchAt ans ω r) : ℕ) : ℕ∞)
  else ⊤

/-- Read an answer from a completed round, returning `none` if the round or query is absent. -/
def transcriptAnswer {Q A : Type} (h : Transcript Q A) (r : ℕ) (q : Q) : Option A :=
  match h[r]? with
  | none => none
  | some rec => if hq : q ∈ rec.1 then some (rec.2 ⟨q, hq⟩) else none

/-- Every recovery call is in the domain guaranteed by (A2). No termination or cost guarantee
for `Rec` is assumed outside this domain. -/
def RecoveryCallsValid {E O : Type} (P : Protocol (IQuery E) (IAnswer E) O)
    (I : Finset E → Prop) (ans : IQuery E → IAnswer E) (ω : Tape) : Prop :=
  ∀ r : ℕ, (r : ℕ∞) < P.rounds ans ω → ∀ B x, IQuery.recover B x ∈ P.batchAt ans ω r →
    I B ∧ x ∉ B ∧ ¬ I (insert x B)

end ExactParallelSampling.QuasiUniform



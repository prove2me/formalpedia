-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_Model
-- name    : ITPIRPreproc_MatchVec_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:08.720318+00:00
-- url     : https://prove2.me/theorems/acbebb06-c96f-4f43-850b-240f3acdecc9
-- title:
--   §3 — single-server PIR with client preprocessing: syntax, experiment, perfect privacy, correctness, costs
-- statement:
--   A **single-server PIR scheme with client preprocessing** for databases $D\in\{0,1\}^n$ and security parameter $\lambda$ consists of five programs of the word RAM, the same programs for every $n$ and $\lambda$, which receive $n$ and $\lambda$ in a header (both parties know them):
--
--   1. $\mathsf{Preprocess}(1^\lambda,D)$, randomized and *streaming*: it reads $D$ once, one bit at a time, and outputs the initial client state.
--   2. $\mathsf{Query}(\mathit{state},i)$, randomized: it outputs a query $Q$ and a private state $\widehat{\mathit{state}}$; only $Q$ is sent.
--   3. $\mathsf{Answer}(D,Q)$, deterministic, with random access to $D$ and nothing else (the server stores only $D$): it returns $\mathit{ans}=(\mathit{ans}_{\rm on},\mathit{ans}_{\rm off})$.
--   4. An online decoder, deterministic, computing $y\in\{0,1\}\cup\{\bot\}$ from $(\widehat{\mathit{state}},\mathit{ans}_{\rm on})$ only.
--   5. A state update, deterministic, computing $\mathit{state}'$ from $(\widehat{\mathit{state}},\mathit{ans}_{\rm on},\mathit{ans}_{\rm off})$.
--
--   Items 4 and 5 together are the paper's $\mathsf{Decode}(\widehat{\mathit{state}},\mathit{ans})=(y,\mathit{state}')$, with the online answer sufficing to decode $y$.
--
--   **Experiment.** For a database $D$, the client runs $\mathit{state}\leftarrow\mathsf{Preprocess}(1^\lambda,D)$. In retrieval protocol $j=1,2,\dots$ an adversary chooses $i_j\in[n]$ as a function of its own coins and the queries $Q_1,\dots,Q_{j-1}$ (adaptively; it is randomized through its coin tape, as a measurable function of it), and the protocol runs with an honest server; the adversary never sees $y_j$ or the states. All coins are independent fair bits.
--
--   **Perfect privacy.** For every $D$ there is a simulator, seeing $n,\lambda,D$ but no index, with a law $\mathrm{sim}_T$ of $T$ queries such that for every adversary, every $T$, every measurable set $B$ of adversary coin tapes and every list $q$ of queries,
--   $$\Pr[\text{adversary coins}\in B\ \wedge\ (Q_1,\dots,Q_T)=q]=\Pr[B]\cdot\mathrm{sim}_T(q).$$
--
--   **Correctness with error $\mathrm{err}$.** For every $D$, adversary and $T$, $\Pr[\exists j\le T:\ y_j\ne D[i_j]]\le \mathrm{err}(T)$; an output $\bot$ counts as a failure.
--
--   **Costs, worst case.** For every database, every coin outcome of $\mathsf{Preprocess}$, every reachable client state, every index and every coin outcome of $\mathsf{Query}$, all programs halt, and: preprocessing client work and storage (header plus working bits; the stream is not stored) are within given budgets; and in each retrieval protocol, online communication $|Q|+|\mathit{ans}_{\rm on}|$, offline communication $|\mathit{ans}_{\rm off}|$, client work (the work of $\mathsf{Query}$, the decoder and the update), server work (the work of $\mathsf{Answer}$) and client storage (for each client program, the input it holds — state, private state, answers — plus its working bits) are within given budgets.
--
--   This is the model in which Theorem 6.1 and Lemma 4.2 are stated.
--
--   **Formalization Note** A randomized adversary is a measurable function of its coin tape; the database is quantified universally, which covers an adversary that chooses it at random. The simulator is given by its law on the first $T$ queries, for every $T$; equality for every $T$ is the same as the existence of a stateful simulator emitting the queries one by one.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), §3 "Definition of PIR with Client Preprocessing", printed pp.9–10 (PDF pp.11–12), protocol (2), "Privacy and Correctness", "Efficiency", footnote 5

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_Machine

open MeasureTheory
open scoped ENNReal

namespace ITPIRPreproc.MatchVec

open WordRAM

/-!
# Single-server PIR with client preprocessing (§3, printed pp.9–10)

A scheme consists of programs of the word RAM (`Def_ITPIRPreproc_MatchVec_Machine`). It is
**one uniform program family**: the same five programs serve every database length `n` and
security parameter `λ`, which they receive in a header `encNat n ++ encNat λ` (both parties
know `n` and `λ`; nothing else, in particular not `T`, is ever given to the scheme).

* `preprocess` — `state ← Preprocess(1^λ, D)`, randomized, reading the database `D` as one
  stream, one bit at a time (it must be `Streaming`, i.e. never use random access).
* `query` — `(Q, ŝtate) ← Query(state, i)`, randomized; its output is `encBits Q ++ ŝtate`.
* `answer` — `ans = Answer(D, Q)`, deterministic, with random access to `D` and nothing else:
  the server stores only `D`. Its output is `encBits ans_on ++ ans_off`.
* `decodeOnline` — computes `y ∈ {0,1} ∪ {⊥}` from `(ŝtate, ans_on)` only (deterministic);
  the online answer suffices to decode `y`.
* `update` — computes `state′` from `(ŝtate, ans_on, ans_off)` (deterministic).

The paper's `Decode(ŝtate, ans) = (y, state′)` is the pair (`decodeOnline`, `update`).

**Experiment.** All randomness comes from a family of independent fair-coin tapes indexed by
`ℕ × ℕ`; tape `0` belongs to the adversary, tape `1` to `Preprocess`, tape `j + 2` to the `Query`
of retrieval `j`. An adversary (computationally unbounded, adaptive, randomized through its own
tape, as a measurable function of it) chooses each index from its coins and the queries seen so
far; it never sees `y_j` or the client states. The database `D` is quantified outside (the adversary's choice of `D`).
-/

/-- A single-server preprocessing PIR scheme: five word-RAM programs. -/
structure Scheme where
  preprocess : Program
  query : Program
  answer : Program
  decodeOnline : Program
  update : Program

/-- The syntactic requirements of §3: streaming preprocessing, deterministic `Answer` and
`Decode`. -/
structure Scheme.WellFormed (S : Scheme) : Prop where
  preprocess_streaming : Streaming S.preprocess
  answer_det : Deterministic S.answer
  decodeOnline_det : Deterministic S.decodeOnline
  update_det : Deterministic S.update

/-- The public header: database length and security parameter. -/
def header (n lam : ℕ) : List Bool :=
  encNat n ++ encNat lam

/-- Input of `Preprocess`: the header, then the database streamed one bit at a time. -/
def preInput (n lam : ℕ) (D : Fin n → Bool) : List Bool :=
  header n lam ++ List.ofFn D

/-- Input of `Query`: header, index, state. -/
def queryInput (n lam : ℕ) (st : List Bool) (i : Fin n) : List Bool :=
  header n lam ++ encNat i.val ++ st

/-- Input of `Answer`: header, query, database. -/
def answerInput (n lam : ℕ) (D : Fin n → Bool) (Q : List Bool) : List Bool :=
  header n lam ++ encBits Q ++ List.ofFn D

/-- Input of the online decoder: header, online answer, private query state. -/
def decodeInput (n lam : ℕ) (ansOn qst : List Bool) : List Bool :=
  header n lam ++ encBits ansOn ++ qst

/-- Input of the state update: header, online and offline answers, private query state. -/
def updateInput (n lam : ℕ) (ansOn ansOff qst : List Bool) : List Bool :=
  header n lam ++ encBits ansOn ++ encBits ansOff ++ qst

/-- The record of one retrieval protocol. -/
structure Round (n : ℕ) where
  /-- The target index `i`. -/
  index : Fin n
  /-- The state before the protocol. -/
  stateIn : List Bool
  /-- The query `Q` (the only client message). -/
  query : List Bool
  /-- The private query state `ŝtate`. -/
  qstate : List Bool
  /-- The online answer `ans_on`. -/
  ansOn : List Bool
  /-- The offline answer `ans_off`. -/
  ansOff : List Bool
  /-- The client's output `y` (`none` is `⊥`). -/
  output : Option Bool
  /-- The updated state `state′`. -/
  stateOut : List Bool

/-- One retrieval protocol (2) for index `i`, from state `st`, with query coins `τ`. -/
noncomputable def runRound (S : Scheme) (n lam : ℕ) (D : Fin n → Bool) (st : List Bool)
    (i : Fin n) (τ : ℕ → Bool) : Round n :=
  let qo := output S.query (queryInput n lam st i) τ
  let Q := (unpair qo).1
  let qst := (unpair qo).2
  let a := output S.answer (answerInput n lam D Q) zeroTape
  let aon := (unpair a).1
  let aoff := (unpair a).2
  { index := i
    stateIn := st
    query := Q
    qstate := qst
    ansOn := aon
    ansOff := aoff
    output := decodeBit (output S.decodeOnline (decodeInput n lam aon qst) zeroTape)
    stateOut := output S.update (updateInput n lam aon aoff qst) zeroTape }

/-- The probability space of the experiment: independent fair-coin tapes indexed by `ℕ × ℕ`. -/
abbrev Tapes := ℕ × ℕ → Bool

/-- Tape number `j`. -/
def tape (ω : Tapes) (j : ℕ) : ℕ → Bool :=
  fun k => ω (j, k)

/-- The law of the tapes: all cells independent fair bits. -/
noncomputable def tapeLaw : Measure Tapes :=
  Measure.infinitePi fun _ : ℕ × ℕ => (PMF.uniformOfFintype Bool).toMeasure

/-- An adaptive, possibly randomized adversary for a fixed database: it maps its coin tape and
the list of queries seen so far to the next index. -/
abbrev Adversary (n : ℕ) := (ℕ → Bool) → List (List Bool) → Fin n

/-- A randomized adversary's choices are events of its coins: for every list of queries seen, the
chosen index is a measurable function of the adversary's coin tape. (Deterministic adversaries,
which ignore their coins, are measurable.) -/
def Adversary.IsMeasurable {n : ℕ} (A : Adversary n) : Prop :=
  ∀ qs : List (List Bool), Measurable fun α : ℕ → Bool => A α qs

/-- The initial client state `Preprocess(1^λ, D)` on tape `1`. -/
noncomputable def initialState (S : Scheme) (n lam : ℕ) (D : Fin n → Bool) (ω : Tapes) :
    List Bool :=
  output S.preprocess (preInput n lam D) (tape ω 1)

/-- The client state before the next protocol, given the rounds so far. -/
noncomputable def currentState (S : Scheme) (n lam : ℕ) (D : Fin n → Bool) (ω : Tapes)
    (h : List (Round n)) : List Bool :=
  match h.getLast? with
  | none => initialState S n lam D ω
  | some r => r.stateOut

/-- The first `T` retrieval protocols of the experiment against adversary `A`. -/
noncomputable def history (S : Scheme) (n lam : ℕ) (D : Fin n → Bool) (A : Adversary n)
    (ω : Tapes) : ℕ → List (Round n)
  | 0 => []
  | j + 1 =>
      let h := history S n lam D A ω j
      h ++ [runRound S n lam D (currentState S n lam D ω h)
              (A (tape ω 0) (h.map Round.query)) (tape ω (j + 2))]

/-- **Perfect privacy** (§3): there is a simulator, which sees `n`, `λ` and `D` but never an
index, whose law of the first `T` queries `sim T` matches the experiment: for every (measurable)
adversary,
every `T`, every measurable set `B` of adversary coin tapes and every query list `qs`,
`Pr[adversary coins ∈ B ∧ (Q_1, …, Q_T) = qs] = Pr[B] · sim T qs`, i.e. the adversary's view
(its coins and the queries) is distributed as independent coins and simulated queries. -/
def PerfectlyPrivate (S : Scheme) (n lam : ℕ) : Prop :=
  ∀ D : Fin n → Bool, ∃ sim : ℕ → List (List Bool) → ℝ≥0∞,
    ∀ (A : Adversary n), A.IsMeasurable → ∀ (T : ℕ) (B : Set (ℕ → Bool)), MeasurableSet B →
      ∀ qs : List (List Bool),
        tapeLaw {ω | tape ω 0 ∈ B ∧ (history S n lam D A ω T).map Round.query = qs} =
          coinTape B * sim T qs

/-- **Correctness with error `err`** (§3): for every database, (measurable) adversary and number `T` of
retrieval protocols, the probability that some `y_j ≠ D[i_j]` (an output `⊥` counts as a
failure) is at most `err T`. -/
def Correct (S : Scheme) (n lam : ℕ) (err : ℕ → ℝ≥0∞) : Prop :=
  ∀ (D : Fin n → Bool) (A : Adversary n), A.IsMeasurable → ∀ T : ℕ,
    tapeLaw {ω | ∃ r ∈ history S n lam D A ω T, r.output ≠ some (D r.index)} ≤ err T

/-- States reachable in the experiment for database `D`: the output of `Preprocess` on any
coins, and the updated state of a protocol run from a reachable state, for any index and any
query coins. -/
inductive Reachable (S : Scheme) (n lam : ℕ) (D : Fin n → Bool) : List Bool → Prop
  | init (τ : ℕ → Bool) : Reachable S n lam D (output S.preprocess (preInput n lam D) τ)
  | step {st : List Bool} (hst : Reachable S n lam D st) (i : Fin n) (τ : ℕ → Bool) :
      Reachable S n lam D (runRound S n lam D st i τ).stateOut

/-- Worst-case cost budgets for one `(n, λ)`. -/
structure Budget where
  /-- Client work of the initial preprocessing. -/
  preWork : ℝ
  /-- Client storage during the initial preprocessing. -/
  preSpace : ℝ
  /-- Online communication `|Q| + |ans_on|` per retrieval protocol. -/
  online : ℝ
  /-- Offline communication `|ans_off|` per retrieval protocol. -/
  offline : ℝ
  /-- Client work (`Query` and `Decode`) per retrieval protocol. -/
  clientWork : ℝ
  /-- Client storage during each retrieval protocol (state and all temporary values). -/
  clientSpace : ℝ
  /-- Server work (`Answer`) per retrieval protocol. -/
  serverWork : ℝ

/-- The scheme meets the budget **in the worst case** at `(n, λ)`: for every database, every
coin outcome of `Preprocess`, every reachable state, every index and every coin outcome of
`Query`, all programs halt and

* preprocessing: client work `cost(Preprocess) ≤ preWork`, client storage (header plus working
  bits; the database arrives as a stream and is not stored) `≤ preSpace`;
* each retrieval protocol: `|Q| + |ans_on| ≤ online`, `|ans_off| ≤ offline`,
  `cost(Query) + cost(decodeOnline) + cost(update) ≤ clientWork`, server work
  `cost(Answer) ≤ serverWork`, and for each client program the input it holds (state, private
  query state, answers) plus its working bits is `≤ clientSpace`. -/
def MeetsBudget (S : Scheme) (n lam : ℕ) (B : Budget) : Prop :=
  ∀ D : Fin n → Bool,
    (∀ τ : ℕ → Bool,
      Halts S.preprocess (preInput n lam D) τ ∧
      (cost S.preprocess (preInput n lam D) τ : ℝ) ≤ B.preWork ∧
      (((header n lam).length + workingBits S.preprocess (preInput n lam D) τ : ℕ) : ℝ) ≤
        B.preSpace) ∧
    ∀ st : List Bool, Reachable S n lam D st → ∀ (i : Fin n) (τ : ℕ → Bool),
      let r := runRound S n lam D st i τ
      let qi := queryInput n lam st i
      let ai := answerInput n lam D r.query
      let di := decodeInput n lam r.ansOn r.qstate
      let ui := updateInput n lam r.ansOn r.ansOff r.qstate
      (Halts S.query qi τ ∧ Halts S.answer ai zeroTape ∧
        Halts S.decodeOnline di zeroTape ∧ Halts S.update ui zeroTape) ∧
      ((r.query.length + r.ansOn.length : ℕ) : ℝ) ≤ B.online ∧
      (r.ansOff.length : ℝ) ≤ B.offline ∧
      ((cost S.query qi τ + cost S.decodeOnline di zeroTape + cost S.update ui zeroTape : ℕ) :
        ℝ) ≤ B.clientWork ∧
      ((qi.length + workingBits S.query qi τ : ℕ) : ℝ) ≤ B.clientSpace ∧
      ((di.length + workingBits S.decodeOnline di zeroTape : ℕ) : ℝ) ≤ B.clientSpace ∧
      ((ui.length + workingBits S.update ui zeroTape : ℕ) : ℝ) ≤ B.clientSpace ∧
      (cost S.answer ai zeroTape : ℝ) ≤ B.serverWork

end ITPIRPreproc.MatchVec



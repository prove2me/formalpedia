-- Prove2me | Definitions.Def_IPPComplexities_Unconditional_Supplement_transcripts
-- name    : IPPComplexities_Unconditional_Supplement_transcripts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:24:45.324835+00:00
-- url     : https://prove2.me/theorems/f428920c-0e31-427d-a7ad-ad6718d7299a
-- title:
--   Transcripts, rounds, prover bits, randomness complexity and perfect completeness
-- statement:
--   Complexity measures of Theorem 1.4 on the published interaction model.
--
--   A **run** records the verdict, the number of oracle queries and the public transcript, each transcript entry tagged with its sender (verifier or prover). Runs are produced by the published execution recursion step for step; the file proves that forgetting the transcript except its length gives exactly the published execution (`runs_map_toOutcome`), so the verdicts and costs are the published ones.
--
--   1. The **prover bits** of a run are the transcript entries sent by the prover.
--   2. The **rounds** of a run are the maximal blocks of consecutive prover bits in its transcript: each round is a verifier message followed by a prover message, and a prover message is a maximal block of prover bits. Queries are not on the transcript and do not count.
--   3. A verifier has **at most $k$ rounds** (resp. **at most $p$ prover bits**, **at most $q$ queries**) if every run in the support, for every input and every prover, satisfies the bound.
--   4. A verifier has **randomness complexity at most $R$** if its law on plans is the image of the uniform distribution on $\{0,1\}^R$; for $R=0$ it is a deterministic verifier.
--   5. A system $V$ has **perfect completeness** for $L$ if every $x\in L$ has a prover that $V$ accepts with probability exactly $1$.
--
--   **Formalization Note** One notion of round is used for every verifier, so the hypothesis and conclusion of Theorem 1.4 are measured alike. A message sent by the prover before any verifier message counts as a round.
-- source:
--   Noga Amit, Oded Goldreich, STOC 2027 submission #297 (October 2026), p. 3, Theorem 1.4 (PDF p. 5); rounds and perfect completeness p. 5–6, §2 (PDF pp. 7–8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/297.pdf

import Definitions.Def_IPPComplexities_Unconditional_validity

namespace IPPComplexities.Unconditional.Supplement

/-- A run of the interaction recorded with its public transcript. Each transcript entry
is `(fromVerifier, bit)`: `true` for a bit sent by the verifier, `false` for a bit sent
by the prover. -/
structure Run where
  verdict : Bool
  queries : ℕ
  transcript : List (Bool × Bool)

def Run.addQuery (r : Run) : Run := {r with queries := r.queries + 1}
def Run.push (d b : Bool) (r : Run) : Run := {r with transcript := (d, b) :: r.transcript}

/-- Forgetting the transcript except its length gives the published `Outcome`. -/
def Run.toOutcome (r : Run) : Outcome := ⟨r.verdict, r.queries, r.transcript.length⟩

/-- The published `play` recursion, step for step, additionally recording the
direction-tagged transcript. -/
noncomputable def playT {n : ℕ} (x : Input n) (P : Prover) :
    Plan n → List Bool → PMF Run
  | .halt b, _ => PMF.pure ⟨b, 0, []⟩
  | .query i l r, t =>
      if x i then (playT x P r t).map Run.addQuery else (playT x P l t).map Run.addQuery
  | .send b s, t => (playT x P s (t ++ [b])).map (Run.push true b)
  | .receive l r, t => (P t).bind fun b =>
      if b then (playT x P r (t ++ [true])).map (Run.push false true)
      else (playT x P l (t ++ [false])).map (Run.push false false)

/-- The runs of a verifier against a prover on an input. -/
noncomputable def runs {n : ℕ} (V : Verifier n) (x : Input n) (P : Prover) : PMF Run :=
  V.law.bind fun s => playT x P s.val []

theorem playT_map_toOutcome {n : ℕ} (x : Input n) (P : Prover) :
    ∀ (s : Plan n) (t : List Bool), (playT x P s t).map Run.toOutcome = play x P s t := by
  have hq : ∀ p : PMF Run, (p.map Run.addQuery).map Run.toOutcome =
      (p.map Run.toOutcome).map addQuery := by
    intro p; rw [PMF.map_comp, PMF.map_comp]; rfl
  have hb : ∀ (d b : Bool) (p : PMF Run), (p.map (Run.push d b)).map Run.toOutcome =
      (p.map Run.toOutcome).map addBit := by
    intro d b p; rw [PMF.map_comp, PMF.map_comp]; rfl
  intro s
  induction s with
  | halt b => intro t; simp only [playT, play, PMF.pure_map]; rfl
  | query i l r ihl ihr =>
    intro t
    by_cases hx : x i = true
    · simp only [playT, play, hx, if_true, hq, ihr]
    · simp only [playT, play, hx, Bool.false_eq_true, if_false, hq, ihl]
  | send b s ih =>
    intro t
    simp only [playT, play, hb, ih]
  | receive l r ihl ihr =>
    intro t
    simp only [playT, play, PMF.map_bind]
    congr 1
    funext b
    cases b
    · simp only [Bool.false_eq_true, if_false, hb, ihl]
    · simp only [if_true, hb, ihr]

/-- The recorded runs agree with the published `execution` on verdict, queries and
total communication. -/
theorem runs_map_toOutcome {n : ℕ} (V : Verifier n) (x : Input n) (P : Prover) :
    (runs V x P).map Run.toOutcome = execution V x P := by
  simp only [runs, execution, PMF.map_bind, playT_map_toOutcome]

/-- Number of bits sent by the prover in a run. -/
def Run.proverBits (r : Run) : ℕ := (r.transcript.filter (fun e => !e.1)).length

/-- Number of maximal blocks of consecutive prover bits in a transcript; `prev` says
whether the preceding entry was a prover bit. -/
def proverBlocks : Bool → List (Bool × Bool) → ℕ
  | _, [] => 0
  | prev, e :: rest =>
      if !e.1 && !prev then proverBlocks true rest + 1 else proverBlocks (!e.1) rest

/-- Rounds of a run: the number of prover messages, a prover message being a maximal
block of consecutive prover bits on the public transcript (each round is a verifier
message followed by a prover message). -/
def Run.rounds (r : Run) : ℕ := proverBlocks false r.transcript

/-- At most `k` rounds, over every input, every prover and every supported run. -/
def AtMostRounds {n : ℕ} (V : Verifier n) (k : ℕ) : Prop :=
  ∀ (x : Input n) (P : Prover) (r : Run), r ∈ (runs V x P).support → r.rounds ≤ k

/-- The prover sends at most `p` bits, over every input, prover and supported run. -/
def ProverBitsBounded {n : ℕ} (V : Verifier n) (p : ℕ) : Prop :=
  ∀ (x : Input n) (P : Prover) (r : Run), r ∈ (runs V x P).support → r.proverBits ≤ p

/-- The verifier makes at most `q` queries, over every input, prover and supported run. -/
def QueriesBounded {n : ℕ} (V : Verifier n) (q : ℕ) : Prop :=
  ∀ (x : Input n) (P : Prover) (r : Run), r ∈ (runs V x P).support → r.queries ≤ q

/-- Randomness complexity at most `R`: the verifier's law on plans is the image of
`R` uniform random bits (for `R = 0`, a point mass, i.e. a deterministic verifier). -/
def RandomnessAtMost {n : ℕ} (V : Verifier n) (R : ℕ) : Prop :=
  ∃ f : (Fin R → Bool) → {s : Plan n // compatible V.turn s [] = true},
    V.law = (PMF.uniformOfFintype (Fin R → Bool)).map f

/-- Perfect completeness: every member of `L` has a prover that is accepted with
probability exactly one. -/
def PerfectCompleteness (L : Property) (V : System) : Prop :=
  ∀ (n : ℕ) (x : Input n), inputList x ∈ L →
    ∃ P : Prover, verdictProbability (V n) x P true = 1

end IPPComplexities.Unconditional.Supplement



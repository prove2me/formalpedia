-- Prove2me | Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
-- name    : IsRandomnessNecessaryADA_Plain_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:48.242491+00:00
-- url     : https://prove2.me/theorems/f3663c11-f0d9-4cdf-b9d4-25bc378c7b2f
-- title:
--   Sample-based adaptive interaction and distributional accuracy
-- statement:
--   A statistical query on a domain $X$ is a function $q:X\to[0,1]$; a Boolean query takes values in $\{0,1\}$. A dataset is an ordered tuple $S\in X^n$. A transcript lists queries and arbitrary real answers in chronological order. A deterministic mechanism receives $S$, the preceding transcript, and the entire current query. An analyst receives only the preceding transcript. Replaying prescribed queries recomputes the mechanism's answers separately for each candidate dataset.
--
--   For a probability mass function $P$, sampling uses the recursive product law $P^n$, permitting repeated entries. The interaction law is its pushforward under the actual adaptive interaction. The population mean and error event are
--   $$Pq=\sum_{x\in X}P(x)q(x),\qquad E_{P,\varepsilon}=\{T:\exists(q,a)\in T,\ |a-Pq|>\varepsilon\}.$$
--   Accuracy means $\Pr(E_{P,\varepsilon})\le1/10$ for every $P$ and analyst. An injection $e:[N]\hookrightarrow X$ specifies the uniform law on exactly its $N$ image points. Probabilities are PMF outer-measure probabilities, so all transcript events are defined without imposing measurability restrictions on response functions. This is reusable interaction infrastructure; no attack or success guarantee is assumed.
-- source:
--   Edith Cohen, Haim Kaplan, Yishay Mansour, Shay Sapir, Uri Stemmer, Eliad Tsfadia, STOC 2027 submission #267 (October 2026), Definitions 2.1–2.2, pp.7–8; Theorem 1.2, p.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/267.pdf; PDF/printed pages coincide.

import Mathlib

set_option autoImplicit false

namespace IsRandomnessNecessaryADA.Plain

/-- Definition 2.1, pp.7–8: statistical queries take values in [0,1]. -/
abbrev StatisticalQuery (X : Type) := X → Set.Icc (0 : ℝ) 1
abbrev BooleanQuery (X : Type) := X → Bool
abbrev Transcript (Q : Type) := List (Q × ℝ)

/-- A response may use the ordered sample, the entire history and full current query.
There is no target-distribution argument. Generic in the query interface. -/
abbrev Response (X Q : Type) (n : ℕ) := (Fin n → X) → Transcript Q → Q → ℝ
abbrev Strategy (Q : Type) := Transcript Q → Q
abbrev Mechanism (X : Type) (n : ℕ) := Response X (StatisticalQuery X) n
abbrev Analyst (X : Type) := Strategy (StatisticalQuery X)
abbrev BooleanAnalyst (X : Type) := Transcript (StatisticalQuery X) → BooleanQuery X

noncomputable def bitValue (b : Bool) : ℝ := if b then 1 else 0

noncomputable def liftQuery {X : Type} (q : BooleanQuery X) : StatisticalQuery X :=
  fun x => ⟨bitValue (q x), by cases q x <;> norm_num [bitValue]⟩

noncomputable def liftAnalyst {X : Type} (A : BooleanAnalyst X) : Analyst X :=
  fun T => liftQuery (A T)

/-- Chronological deterministic replay of prescribed past queries. -/
def replayQueries {X Q : Type} {n : ℕ} (m : Response X Q n)
    (s : Fin n → X) (h : List Q) : Transcript Q :=
  h.foldl (fun T q => T ++ [(q, m s T q)]) []

/-- The analyst has history only, and no sample input. -/
def interaction {X Q : Type} {n : ℕ} (m : Response X Q n) (A : Strategy Q)
    (s : Fin n → X) : ℕ → Transcript Q
  | 0 => []
  | k + 1 =>
    let T := interaction m A s k
    let q := A T
    T ++ [(q, m s T q)]

/-- Ordered independent draws with replacement; each recursive step uses a fresh draw. -/
noncomputable def iid {X : Type} (p : PMF X) : (n : ℕ) → PMF (Fin n → X)
  | 0 => PMF.pure Fin.elim0
  | n + 1 => p.bind (fun x => (iid p n).map (Fin.cons x))

/-- PMF outer measure is defined on every set, including sets of real transcripts. -/
noncomputable def probability {Ω : Type} (p : PMF Ω) (E : Set Ω) : ℝ :=
  (p.toOuterMeasure E).toReal

noncomputable def interactionLaw {X Q : Type} {n : ℕ} (m : Response X Q n)
    (A : Strategy Q) (p : PMF X) (k : ℕ) : PMF (Transcript Q) :=
  (iid p n).map (fun s => interaction m A s k)

/-- Population expectation, never the empirical average. -/
noncomputable def populationMean {X : Type} [Fintype X] (p : PMF X)
    (q : StatisticalQuery X) : ℝ := ∑ x, (p x).toReal * (q x).val

noncomputable def errorEvent {X : Type} [Fintype X] (p : PMF X) (ε : ℝ) :
    Set (Transcript (StatisticalQuery X)) :=
  {T | ∃ qa ∈ T, ε < |qa.2 - populationMean p qa.1|}

/-- Definition 2.2 for deterministic mechanisms and analysts. Mixing analysts does not
change this universal accuracy condition. This predicate is never a goal hypothesis. -/
noncomputable def IsAccurate {X : Type} [Fintype X] {n : ℕ}
    (m : Mechanism X n) (ε : ℝ) (k : ℕ) : Prop :=
  0 < ε ∧ ∀ (p : PMF X) (A : Analyst X),
    probability (interactionLaw m A p k) (errorEvent p ε) ≤ 1 / 10

/-- Uniform law on an explicitly injected support; every support point is distinct. -/
noncomputable def uniformFin (N : ℕ) (hN : 0 < N) : PMF (Fin N) := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  exact PMF.uniformOfFintype (Fin N)

noncomputable def uniformSupport {X : Type} {N : ℕ} (hN : 0 < N)
    (e : Fin N ↪ X) : PMF X := (uniformFin N hN).map e

end IsRandomnessNecessaryADA.Plain



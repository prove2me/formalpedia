-- Prove2me | Definitions.Def_QuerySampleRev_transcript
-- name    : QuerySampleRev_transcript
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:47.091492+00:00
-- url     : https://prove2.me/theorems/d5c896df-2234-44bf-b423-566feba39771
-- title:
--   Run of a learner: stopping time, output, counts $S$, $T$, $T^{(i)}$ and transcript
-- statement:
--   Fix a learner and an outcome $\omega=(u,v)$. Running the learner gives the following quantities.
--   1. The **stopping time** $\tau\in\{0,1,\dots\}\cup\{\infty\}$, the first round whose action is a stop; $\tau=\infty$ if the learner never stops.
--   2. The **output price** $p^A$, the price of the stop action at round $\tau$, meaningful when $\tau<\infty$.
--   3. The **sample count** $S$, the number of sample rounds $t<\tau$.
--   4. For a set of prices $P$, the count $T^{(P)}$ of query rounds $t<\tau$ whose price lies in $P$. The total **query count** is $T=T^{(\mathbb R)}$.
--   5. The **transcript**: the seed $u$ and, for each round $t<\tau$, the observation of round $t$ (a sample value, or a query price with its feedback). The entries from round $\tau$ on are blank.
--
--   All counts take values in $\{0,1,\dots\}\cup\{\infty\}$. The transcript records the access types, samples, query prices and feedback; the final output is a function of it (§2.3).
--
--   **Formalization Note** The transcript also records the internal seed, so its σ-algebra is finer than the paper's.
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), §2.2, p.13 (PDF p.15); §2.3, p.14 (PDF p.16), definition of the transcript; Claim 2, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_QuerySampleRev_Learner

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev

/-- The observation produced by action `a` when the round's value draw is `x`: a sample reveals `x`, a
query at `p` reveals `(p, 1[x ≥ p])`; a stop action produces a dummy observation that is never part of
the transcript. -/
noncomputable def observe : Act → ℝ → Obs
  | Sum.inl _, x => Sum.inl x
  | Sum.inr (Sum.inl p), x => Sum.inr (p, decide (p ≤ x))
  | Sum.inr (Sum.inr _), _ => Sum.inl 0

/-- The history of observations of rounds `0, …, t − 1` when learner `L` runs with seed `u` on the value
stream `v`. -/
noncomputable def hist (L : Learner) (u : unitInterval) (v : ℕ → ℝ) : (t : ℕ) → Fin t → Obs
  | 0 => Fin.elim0
  | t + 1 => Fin.snoc (hist L u v t) (observe (L.act t u (hist L u v t)) (v t))

/-- The action taken at round `t` on the outcome `ω = (u, v)`. -/
noncomputable def actAt (L : Learner) (ω : Outcome) (t : ℕ) : Act :=
  L.act t ω.1 (hist L ω.1 ω.2 t)

/-- The stopping round `τ ∈ ℕ ∪ {∞}`: the first round whose action is a stop action, `⊤` if the learner
never stops. -/
noncomputable def stopTime (L : Learner) (ω : Outcome) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : ∃ p, actAt L ω t = Act.stop p), (t : ℕ∞)

/-- The output price `p^A`: the price of the stop action at round `τ`. Meaningful only when `τ < ⊤`
(otherwise the junk value is the price read at round `0`, and every statement guards with `τ < ⊤`). -/
noncomputable def output (L : Learner) (ω : Outcome) : ℝ :=
  match actAt L ω (stopTime L ω).toNat with
  | Sum.inr (Sum.inr p) => p
  | _ => 0

/-- **Sample count `S`.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization*
(manuscript, sha256 c31ea3d3…), §2.2, p.13 (PDF 15): "We denote the number of value samples by `S`".
The number of sample rounds before the stopping round, in `ℕ∞` (`⊤` if the learner samples forever). -/
noncomputable def sampleCount (L : Learner) (ω : Outcome) : ℕ∞ :=
  {t : ℕ | (t : ℕ∞) < stopTime L ω ∧ actAt L ω t = Act.sample}.encard

/-- **Query count in a price set, `T⁽ⁱ⁾`.** Same source, Claim 2, p.14 (PDF 16) and Lemma 10, p.23
(PDF 25): the number of pricing queries with prices in the set `P`, before the stopping round, in `ℕ∞`. -/
noncomputable def queryCountIn (L : Learner) (P : Set ℝ) (ω : Outcome) : ℕ∞ :=
  {t : ℕ | (t : ℕ∞) < stopTime L ω ∧ ∃ p ∈ P, actAt L ω t = Act.query p}.encard

/-- **Query count `T`.** Same source, §2.2, p.13: "the number of pricing queries" (written `Q` in §2.2
and `T` in §5.5): the number of query rounds before the stopping round, in `ℕ∞`. -/
noncomputable def queryCount (L : Learner) (ω : Outcome) : ℕ∞ :=
  queryCountIn L Set.univ ω

/-- **Transcript.** Same source, §2.3, p.14 (PDF 16): "The transcript records the access types, observed
samples, query prices, query feedback, and final output."

The transcript of the run on `ω = (u, v)` is the seed `u` together with the sequence whose `t`-th entry is
the observation of round `t` (`Sum.inl`) for `t < τ` and the blank `Sum.inr ()` from round `τ` on. Access
types, samples, query prices and feedback are read off the observations, and the final output is the
stop action at round `τ`, a function of the seed and the observations before `τ`.

**Formalization Note.** Recording the seed makes the transcript σ-algebra finer than the paper's (every
event of the paper's transcript is a transcript event here). -/
noncomputable def transcript (L : Learner) (ω : Outcome) : unitInterval × (ℕ → Obs ⊕ Unit) :=
  (ω.1, fun t => if (t : ℕ∞) < stopTime L ω then Sum.inl (hist L ω.1 ω.2 (t + 1) (Fin.last t))
    else Sum.inr ())

end QuerySampleRev



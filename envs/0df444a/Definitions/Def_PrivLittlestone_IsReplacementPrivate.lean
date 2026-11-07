-- Prove2me | Definitions.Def_PrivLittlestone_IsReplacementPrivate
-- name    : PrivLittlestone_IsReplacementPrivate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:26:59.928545+00:00
-- url     : https://prove2.me/theorems/ca0f6947-0528-46a6-b953-c2140241c387
-- title:
--   $(\varepsilon,\delta)$-privacy under replacement on fixed streams
-- statement:
--   An online learner $A$ is **$(\varepsilon, \delta)$-private under replacement** for horizon $T$ if, for every pair of adjacent length-$T$ streams $z, z'$ and every event $E$ of classifier transcripts,
--   $$
--   \mathbb P[A(z) \in E] \le e^{\varepsilon}\, \mathbb P[A(z') \in E] + \delta,
--   $$
--   where $A(z)$ is the transcript $(g_1, \dots, g_T)$ on $z$. Neither stream is required to be realizable.
--
--   **Formalization Note** $E$ ranges over all sets of transcripts (measurable for a regular learner). Adjacency is symmetric, so both orders are covered.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), §2.1, p.4

import Mathlib
import Definitions.Def_PrivLittlestone_transcript
import Definitions.Def_PrivLittlestone_IsAdjacent

namespace PrivLittlestone

open MeasureTheory

/-- **(ε, δ)-privacy under replacement** for fixed streams (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
§2.1, p.4): for every adjacent pair `z, z'` of length-`T` streams and every event `E` of
classifier transcripts, `P[A(z) ∈ E] ≤ e^ε P[A(z') ∈ E] + δ`. Neither stream is required to be
realizable.

**Formalization Note** `E` ranges over all sets of transcripts; for a regular learner
(`OnlineLearner.IsRegular`) all of them are measurable events. Adjacency is symmetric, so both
orders of the pair are covered. -/
def IsReplacementPrivate {X : Type*} (A : OnlineLearner X) (T : ℕ) (ε δ : ℝ) : Prop :=
  ∀ z z' : Fin T → X × Bool, IsAdjacent z z' → ∀ E : Set (Fin T → X → Bool),
    A.μ {ω | transcript A z ω ∈ E} ≤
      ENNReal.ofReal (Real.exp ε) * A.μ {ω | transcript A z' ω ∈ E} + ENNReal.ofReal δ

end PrivLittlestone



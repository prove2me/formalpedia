-- Prove2me | Definitions.Def_SDEConvexOpt_F0Complete
-- name    : SDEConvexOpt_F0Complete
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:00.781435+00:00
-- url     : https://prove2.me/theorems/1b9e131c-610c-43f9-80ef-20ff6f028f0b
-- title:
--   $\mathcal F_0$ contains every $\mathbb P$-null event
-- statement:
--   A filtration $(\mathcal F_t)_{t\ge0}$ on $(\Omega,\mathcal F,\mathbb P)$ has a complete initial $\sigma$-algebra when every event $N\in\mathcal F$ with $\mathbb P(N)=0$ belongs to $\mathcal F_0$ (hence to every $\mathcal F_t$).
--
--   It is the completeness half of the usual conditions under which the existence theorems cited for Theorem A.7 (Øksendal [33, Theorem 5.2.1], Mao [35, Theorem 2.4.1]) are proved.
--
--   **Formalization Note** The paper states no condition on its filtered probability space (pp.2, 7). The mission uses this predicate only as a hypothesis of the existence clauses, where a solution adapted to $(\mathcal F_t)$ with every path continuous must be produced. Right-continuity is not assumed.
-- source:
--   Maulen S., Fadili, Attouch, An SDE perspective on stochastic convex optimization, arXiv:2207.02750v1, Theorem A.7, p.34 (setting of [33], [35]); §2.2, p.7

import Mathlib

open MeasureTheory
open scoped NNReal

namespace SDEConvexOpt

/-- The time-`0` σ-algebra `𝓕₀` of the filtration contains every `ℙ`-null event of `𝓕`
(the completeness half of the usual conditions of Mao [35], cited with Øksendal [33] for the
existence part of Theorem A.7, p.34, of Maulen S., Fadili, Attouch, arXiv:2207.02750v1).

**Formalization Note** The paper states no condition on `(Ω, 𝓕, {𝓕ₜ}, ℙ)` (pp.2, 7); this
predicate is used only as a hypothesis of the existence clauses, where a solution with
continuous paths for every `ω` must be adapted. Right-continuity of the filtration is not
assumed. -/
def F0Complete {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) : Prop :=
  ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[ℱ 0] N

end SDEConvexOpt



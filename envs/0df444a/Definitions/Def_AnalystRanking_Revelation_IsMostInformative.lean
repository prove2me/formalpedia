-- Prove2me | Definitions.Def_AnalystRanking_Revelation_IsMostInformative
-- name    : AnalystRanking_Revelation_IsMostInformative
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:35:23.836186+00:00
-- url     : https://prove2.me/theorems/d45bd0c0-d045-473b-ab71-9572eb42a2ea
-- title:
--   Most informative equilibrium, Definition 2
-- statement:
--   Let $\mathcal E$ be a set of strategy pairs (the equilibria). A pair $e^*\in\mathcal E$ is the **most informative equilibrium** if for every $e\in\mathcal E$
--   $$\sigma^h(e^*)\ge\sigma^h(e)\quad\text{and}\quad\sigma^l(e^*)\ge\sigma^l(e)$$
--   (Definition 2, p. 10). It need not exist, and it is unique when it does.
--
--   **Formalization Note** $\mathcal E$ is a predicate on pairs, instantiated with the competition or the benchmark equilibria. The order is coordinatewise; it is not a maximizer of forecast informativeness.
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Definition 2, p. 10

import Mathlib

namespace AnalystRanking.Revelation

/-- **Most informative equilibrium, Definition 2.**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Definition 2, p. 10: "Suppose `ℰ` is the set of all equilibria. If there exists an
equilibrium `e* ∈ ℰ` such that for any other equilibrium `e ∈ ℰ`, the strategy pairs satisfy
`σʰ(e*) ⩾ σʰ(e)` and `σˡ(e*) ⩾ σˡ(e)`, then `e*` is the most informative equilibrium."

`IsMostInformative E e` holds when `e ∈ E` and `e` dominates every `e' ∈ E` coordinatewise.

**Formalization Note.** `E` is a predicate on strategies `(σʰ, σˡ)`; it is instantiated with
`IsCompEq …` or `IsBenchEq …`. This is a coordinatewise maximum, not a maximizer of `Π`. -/
def IsMostInformative (E : ℝ × ℝ → Prop) (e : ℝ × ℝ) : Prop :=
  E e ∧ ∀ e' : ℝ × ℝ, E e' → e'.1 ≤ e.1 ∧ e'.2 ≤ e.2

end AnalystRanking.Revelation



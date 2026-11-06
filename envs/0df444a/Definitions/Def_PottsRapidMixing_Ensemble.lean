-- Prove2me | Definitions.Def_PottsRapidMixing_Ensemble
-- name    : PottsRapidMixing_Ensemble
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:22.824203+00:00
-- url     : https://prove2.me/theorems/e253d742-b6b3-47ac-8723-82d91b17541c
-- title:
--   Uniform random $\Delta$-regular graphs and "with probability $1-o(1)$"
-- statement:
--   For integers $n,\Delta$, let $\mathcal G_{n,\Delta}$ be the set of simple $\Delta$-regular graphs on the vertex set $\{0,\dots,n-1\}$. A *uniformly random simple $\Delta$-regular graph on $n$ vertices* is a uniform element of $\mathcal G_{n,\Delta}$, so the probability of a property $P$ is
--   $$\frac{|\{G\in\mathcal G_{n,\Delta}: P(G)\}|}{|\mathcal G_{n,\Delta}|}.$$
--   A sequence of properties $(P_n)$ holds *with probability $1-o(1)$* when this ratio tends to $1$ as $n\to\infty$ along the integers $n$ with $n\Delta$ even.
--
--   This is the ensemble of every high-probability statement in the mission.
--
--   **Formalization Note** The set $\mathcal G_{n,\Delta}$ is nonempty exactly when $n\Delta$ is even and $n>\Delta$, which is why the limit runs along $n\Delta$ even; for an empty set the ratio is $0$, and this never matters in the limit. Constants of a statement are always quantified outside the predicate.
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, p.1 (the ensemble), p.2 (Theorem 1.1)

import Mathlib

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- The Δ-regular simple graphs on the vertex set `Fin n`: the sample space of "a uniformly random
simple Δ-regular graph on n vertices" (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.1).

**Formalization Note.** The set is nonempty exactly when `n * Δ` is even and `n > Δ`. -/
noncomputable def regularGraphs (n Δ : ℕ) : Finset (SimpleGraph (Fin n)) :=
  Finset.univ.filter (fun G => G.IsRegularOfDegree Δ)

/-- The probability that a uniformly random simple Δ-regular graph on `Fin n` satisfies `P`
(arXiv:2610.42059, p.1): the fraction of `regularGraphs n Δ` that satisfy it.

**Formalization Note.** When there is no such graph this is `0 / 0 = 0`; `WithHighProb` only looks
at `n` large along `n * Δ` even, where the count is positive. -/
noncomputable def regularProb (n Δ : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (((regularGraphs n Δ).filter P).card : ℝ) / ((regularGraphs n Δ).card : ℝ)

/-- "With probability 1 − o(1), a random Δ-regular graph on n vertices satisfies `P`"
(arXiv:2610.42059, pp.2, 10–14, 23, 31): the probability under the uniform law tends to 1 as
`n → ∞` along the `n` with `n * Δ` even.

**Formalization Note.** Every constant of a statement that uses this predicate is quantified
outside it, so it is fixed before `n` and before the graph. The restriction to `n * Δ` even is the
set of `n` for which the ensemble exists. -/
def WithHighProb (Δ : ℕ) (P : ∀ n : ℕ, SimpleGraph (Fin n) → Prop) : Prop :=
  Tendsto (fun n : ℕ => regularProb n Δ (P n)) (atTop ⊓ 𝓟 {n : ℕ | Even (n * Δ)}) (𝓝 1)

end PottsRapidMixing



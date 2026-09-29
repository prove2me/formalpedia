-- Prove2me | Definitions.Def_CompetitivePaging_LowerBound_uncoveredProb
-- name    : CompetitivePaging_LowerBound_uncoveredProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:17:34.00929+00:00
-- url     : https://prove2.me/theorems/faad2342-19a9-486b-804a-a2ffed381f6a
-- title:
--   The adversary's probability vector $p_i$: probability that vertex $i$ is not covered
-- statement:
--   Let $A$ be a randomized on-line $k$-server algorithm on a metric space $M$, presented as a probability space $(\Omega,\mu)$ of coin outcomes together with, for every outcome $\omega\in\Omega$, a deterministic on-line algorithm $A_\omega$. For a request sequence $\sigma$ write $C_\omega(\sigma)$ for the configuration of $A_\omega$ after it has served $\sigma$.
--
--   For a vertex $i\in M$ the **uncovered probability** of $i$ after $\sigma$ is
--
--   $$
--   p_i(\sigma)\;=\;\mu\bigl(\{\omega\in\Omega : \text{no server of } C_\omega(\sigma) \text{ is located at } i\}\bigr).
--   $$
--
--   The vector $p=(p_i)_{i\in M}$ is the object the adversary maintains in the lower-bound proof of Fiat et al.: it cannot see where $A$'s servers are, but it can compute, for every vertex, the probability that the vertex is not covered. Requesting vertex $i$ costs $A$ at least $p_i$ in expectation on a uniform metric.
--
--   **Formalization Note** The value is the measure of the set of outcomes as a real number (`ENNReal.toReal`). Lean's measure applies to every set (as an outer measure), so the definition needs no measurability; results that use $p$ as a genuine probability assume the event measurable.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 7, §5, proof of Theorem 4 (the vector p = (p_1, …, p_n))

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_randomized

namespace CompetitivePaging.LowerBound

open MeasureTheory

/-- The adversary's **probability vector** (Fiat et al. 1991, §5, proof of Theorem 4, p. 7):
`uncoveredProb A σ i` is the probability `p_i`, over the coin outcomes of the randomized online
algorithm `A`, that vertex `i` is **not** covered by a server of `A` after `A` has served the
request sequence `σ`. It is the measure of the set of outcomes `ω` for which `i` is not among
the positions of the configuration `(A.alg ω).conf σ`, converted to a real number (the measure
is a probability measure, so the value lies in `[0, 1]`). -/
noncomputable def uncoveredProb {k : ℕ} {M : Type*} [MetricSpace M]
    (A : KServer.RandomizedAlgorithm k M) (σ : List M) (i : M) : ℝ :=
  (A.μ {ω | i ∉ Set.range ((A.alg ω).conf σ)}).toReal

end CompetitivePaging.LowerBound



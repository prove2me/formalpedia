-- Prove2me | Definitions.Def_MetricMatchingDistortion_Mechanism
-- name    : MetricMatchingDistortion_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:26.356975+00:00
-- url     : https://prove2.me/theorems/f13538ce-34a6-4db7-a1a5-fe6026323a88
-- title:
--   Randomized ordinal matching mechanism and its expected cost
-- statement:
--   A **randomized matching mechanism** $\mathcal A$ assigns to every $n$ and every ranking profile $\sigma$ on $n$ agents and $n$ items a probability distribution $\mathcal A(\sigma)$ over perfect matchings. It sees only the rankings, never the distances. Its **expected cost** under $d$ is
--   $$\mathbb E_{M\sim\mathcal A(\sigma)}[\mathrm{cost}(M,d)]=\sum_{\pi}\Pr_{\mathcal A(\sigma)}[\pi]\,\mathrm{cost}(\pi,d).$$
--
--   **Formalization Note** The distribution is a `PMF` on `Equiv.Perm (Fin n)`; ordinality is enforced by the type.
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), §2, p.9–10 (PDF pp.11–12)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_Ranking
import Definitions.Def_MetricMatchingDistortion_matchingCost

namespace MetricMatchingDistortion

/-- **Randomized matching mechanism.** Charikar et al., *Sublinear Metric Distortion for Matching*,
arXiv:2611.05777 (held version, sha256 fdf3452b…), §2, p.9 (PDF p.11): "we consider mechanisms
M(σ) that may use randomness in conjunction with the rankings in σ to output a matching. We
identify each randomized matching mechanism with its induced distribution over perfect integral
matchings."

A mechanism maps the number `n` of agents and a ranking profile on `n` agents and `n` items to a
probability distribution over perfect integral matchings `Equiv.Perm (Fin n)`.

**Formalization Note.** The input holds the rankings only, never the metric: a mechanism is
ordinal by its type. -/
abbrev Mechanism := ∀ n : ℕ, Ranking n → PMF (Equiv.Perm (Fin n))

/-- `E_{M∼A(σ)}[cost(M, d)]` (§2, p.10): the expected cost of the mechanism's random perfect
matching on the instance `rk` under the distances `d`. -/
noncomputable def expectedCost (A : Mechanism) (n : ℕ) (rk : Ranking n)
    (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) : ℝ :=
  ∑ π : Equiv.Perm (Fin n), (A n rk π).toReal * matchingCost π d

end MetricMatchingDistortion



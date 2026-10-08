-- Prove2me | Definitions.Def_RobustMNL_Dynamic_StaticModel
-- name    : RobustMNL_Dynamic_StaticModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:20:40.735025+00:00
-- url     : https://prove2.me/theorems/8e2ed5b2-4395-4cfa-aeed-f72487c75e80
-- title:
--   Sec. 3, p. 5 — the MNL choice probabilities φ_i(S, v)
-- statement:
--   A seller has $n$ products $\mathcal A = \{1, \dots, n\}$. Customers choose according to a **multinomial logit model** with parameter vector $v = (v_0, v_1, \dots, v_n) \in \mathbb R^{n+1}_{++}$: $v_0$ is the weight of the no-purchase option and $v_i$ the preference weight of product $i$. If the assortment $S \subseteq \mathcal A$ is offered, a customer buys product $i$ with probability
--   $$\phi_i(S,v) = \begin{cases} \dfrac{v_i}{v_0 + \sum_{\ell \in S} v_\ell} & i \in S,\\[4pt] 0 & \text{otherwise,}\end{cases}$$
--   and buys nothing with the remaining probability $1 - \sum_{i \in S} \phi_i(S, v)$. The expected revenue $f(S, v) = \sum_{i \in S} r_i \phi_i(S, v)$, the worst case $\min_{v \in \mathcal V} f(S, v)$, $Z^*(\mathcal V)$ and the smallest-cardinality optimal assortment $S^*(\mathcal V)$ of Sec. 3 are the shared definitions `RobustMNL.Static.Model` (`rev`, `worst`, `Zstar`, `IsSmallestOptimal`), which this file imports.
--
--   The choice probabilities are needed to write the Bellman equation (Dynamic Robust) of Section 4 in the paper's form.
--
--   **Formalization Note** Products are `Fin n`, so Lean index $i$ is the paper's product $i+1$. A parameter vector is a pair `p : ℝ × (Fin n → ℝ)` with `p.1` $= v_0$ and `p.2 i` $= v_{i+1}$. With these conventions $\sum_{i \in S} r_i \phi_i(S, v)$ equals the published `ChoiceCDLP.MNL.mnlObjective p.2 r p.1 S` for every $p$. $Z^*_\delta, S^*_\delta$ of Sec. 3.1 (p. 10) are `Zstar V (r + δ)` and `IsSmallestOptimal V (r + δ)`.
-- source:
--   Rusmevichientong, Topaloglu, Robust Assortment Optimization in Revenue Management Under the Multinomial Logit Choice Model, Operations Research (2012), doi:10.1287/opre.1120.1063, authors' manuscript of 20 Sep 2011, Sec. 3, pp. 5–6 (φ_i and f, p. 5; (Robust Logit) and S*(V) with footnote 1, p. 6) and Sec. 3.1, p. 10 (Z*_δ, S*_δ)

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_RobustMNL_Static_Model

namespace RobustMNL.Dynamic

/-- The MNL choice probability `φ_i(S, v) = v_i / (v₀ + ∑_{ℓ ∈ S} v_ℓ)` if `i ∈ S`, and `0`
otherwise (Sec. 3, p. 5). -/
noncomputable def choiceProb {n : ℕ} (S : Finset (Fin n)) (p : ℝ × (Fin n → ℝ)) (i : Fin n) : ℝ :=
  if i ∈ S then p.2 i / (p.1 + ∑ ℓ ∈ S, p.2 ℓ) else 0

end RobustMNL.Dynamic



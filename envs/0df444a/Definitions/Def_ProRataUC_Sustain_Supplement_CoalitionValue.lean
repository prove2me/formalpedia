-- Prove2me | Definitions.Def_ProRataUC_Sustain_Supplement_CoalitionValue
-- name    : ProRataUC_Sustain_Supplement_CoalitionValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:23:01.173219+00:00
-- url     : https://prove2.me/theorems/94395abb-9a7d-4b39-9996-77a0abe281da
-- title:
--   App. B.1.4, p. 61 — coalition value f(J): the largest total subscription fee a coalition J of artists collects on a competing platform
-- statement:
--   This definition belongs to Appendix B.1.4 ("Platform's monopoly and the existence of core") of Alaei, Makhdoumi, Malekian and Pekeč, and builds on the published two-type streaming setting `ProRataUC.Sustain.Setting`.
--
--   In that setting there is a finite set $\mathcal M$ of artists and two user types $i\in\{1,2\}$ with usage rates $\lambda_i$, population masses $q_i$, and listening probabilities $\pi_{ij}$ (the probability that a type $i$ user wants artist $j$). Suppose a coalition $J\subseteq\mathcal M$ of artists leaves and forms a competing platform offering only their content. Writing $\pi_{iJ}=\sum_{j\in J}\pi_{ij}$, if the competing platform targets the set $S\subseteq\{1,2\}$ of user types, the largest fee every type in $S$ accepts is $\min_{i\in S}\lambda_i\pi_{iJ}$, collected from mass $\sum_{i\in S}q_i$. The **coalition value** is the best such revenue:
--   $$f(J)=\max_{S\subseteq\{1,2\}}\Big(\min_{i\in S}\lambda_i\sum_{j\in J}\pi_{ij}\Big)\Big(\sum_{i\in S}q_i\Big).$$
--   Written out over the four subsets $S$,
--   $$f(J)=\max\big\{0,\ \lambda_1\pi_{1J}\,q_1,\ \lambda_2\pi_{2J}\,q_2,\ \min(\lambda_1\pi_{1J},\lambda_2\pi_{2J})\,(q_1+q_2)\big\},$$
--   where $S=\emptyset$ contributes $0$ because $\sum_{i\in\emptyset}q_i=0$.
--
--   The function $f$ is the characteristic function of the cooperative game whose core (Definition 4) describes when the platform offering all artists can keep its monopoly.
--
--   **Formalization Note** `coalitionValue s J` takes a `Finset` $J$ of artists and writes the maximum over the four subsets $S\subseteq\{1,2\}$ explicitly as nested `max`. The term for $S=\emptyset$ is taken to be $0$: the empty minimum is multiplied by the empty sum $0$. The factor $q_1+q_2$ for $S=\{1,2\}$ is kept as printed (it equals $1$ under the standing assumptions).
-- source:
--   Alaei, Makhdoumi, Malekian & Pekeč, Revenue-sharing allocation strategies for two-sided media platforms: Pro-rata vs. user-centric, submitted manuscript (SSRN 3645521), p. 61, App. B.1.4, definition of f(J)

import Mathlib
import Definitions.Def_ProRataUC_Sustain_Setting

namespace ProRataUC.Sustain.Supplement

open ProRataUC.Sustain

variable {M : Type*}

/-- The coalition value `f(J)` of App. B.1.4, p. 61:
`f(J) = max_{S ⊆ {1,2}} (min_{i∈S} λ_i Σ_{j∈J} π_ij)(Σ_{i∈S} q_i)`, the largest total subscription
fee a coalition `J` of artists collects on a competing platform. The four subsets `S` are written
out: `S = ∅` contributes `0` (since `Σ_{i∈∅} q_i = 0`), `S = {1}` gives `(λ1 π1J) q1`,
`S = {2}` gives `(λ2 π2J) q2`, and `S = {1,2}` gives `min(λ1 π1J, λ2 π2J)(q1 + q2)`. -/
noncomputable def coalitionValue (s : Setting M) (J : Finset M) : ℝ :=
  max (max 0 (s.lam1 * (∑ j ∈ J, s.pi1 j) * s.q1))
    (max (s.lam2 * (∑ j ∈ J, s.pi2 j) * s.q2)
      (min (s.lam1 * ∑ j ∈ J, s.pi1 j) (s.lam2 * ∑ j ∈ J, s.pi2 j) * (s.q1 + s.q2)))

end ProRataUC.Sustain.Supplement



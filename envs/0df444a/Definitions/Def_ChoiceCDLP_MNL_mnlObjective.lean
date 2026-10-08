-- Prove2me | Definitions.Def_ChoiceCDLP_MNL_mnlObjective
-- name    : ChoiceCDLP_MNL_mnlObjective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T07:42:34.447664+00:00
-- url     : https://prove2.me/theorems/87caf2bb-5737-4a10-8b27-fe8fba1bec55
-- title:
--   Objective (14) of the single-segment MNL offer-set problem: f(S) = (Σ_{j∈S} w_j v_j)/(Σ_{j∈S} v_j + v_0)
-- statement:
--   Fix one customer segment whose **consideration set** is a finite set $\iota$ of products. Under the multinomial logit (MNL) choice model each product $j$ carries a **preference weight** $v_j$, and the option of buying nothing carries the **no-purchase weight** $v_0$. If the firm offers the set $S \subseteq \iota$, a customer of the segment buys product $j \in S$ with probability $v_j/(\sum_{i\in S} v_i + v_0)$. Given a **score** $w_j$ per product (in the paper, the displacement-adjusted revenue $w_j = r_j - \pi^\top A_j$), the expected score collected from one customer when $S$ is offered is
--   $$f(S) = \frac{\sum_{j \in S} w_j v_j}{\sum_{j \in S} v_j + v_0}.$$
--   This is the objective of the paper's problem (14), $\max_{y \in \{0,1\}^{s}} \sum_{j} w_j v_j y_j / (\sum_j v_j y_j + v_0)$, written for offer sets: the binary offer vector $y$ corresponds to $S = \{ j : y_j = 1\}$.
--
--   **Formalization Note.** Offer vectors $y \in \{0,1\}^s$ are represented by subsets `S : Finset ι`. No sign conditions are built into the definition; the theorems state them. When $S = \emptyset$ and $v_0 = 0$ the quotient is $0/0$, which Lean evaluates to $0$; this is exactly the paper's convention $h(0) := 0$ for $v_0 = 0$ (p. 309).
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, pp. 299–300, §6.3 (MNL with disjoint consideration sets) and problem (14) in Proposition 6

import Mathlib

namespace ChoiceCDLP.MNL

/-- The objective of the single-segment MNL offer-set problem (14) of Liu and van Ryzin (2008,
Proposition 6, p. 300), written for an offer set `S` of the consideration set `ι` (the paper's
`y_j = 1` iff `j ∈ S`): with preference weights `v j`, no-purchase weight `v₀` and scores `w j`,
`f(S) = (∑_{j ∈ S} w_j v_j) / (∑_{j ∈ S} v_j + v₀)`.
When `S = ∅` and `v₀ = 0` the quotient is `0 / 0 = 0` in Lean, the paper's convention
`h(0) := 0` (p. 309). -/
noncomputable def mnlObjective {ι : Type*} (v w : ι → ℝ) (v₀ : ℝ) (S : Finset ι) : ℝ :=
  (∑ j ∈ S, w j * v j) / (∑ j ∈ S, v j + v₀)

end ChoiceCDLP.MNL



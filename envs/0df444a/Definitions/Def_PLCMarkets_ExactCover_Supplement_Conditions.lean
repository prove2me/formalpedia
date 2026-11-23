-- Prove2me | Definitions.Def_PLCMarkets_ExactCover_Supplement_Conditions
-- name    : PLCMarkets_ExactCover_Supplement_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:15:47.356588+00:00
-- url     : https://prove2.me/theorems/1c2b1e5b-051f-47b1-a4b9-b6bfa3f7b11b
-- title:
--   The economy graph, condition (C') and nonsatiation (C2) (§6)
-- statement:
--   Let $M$ be an Arrow–Debreu market with agents $B$, goods $G$, endowments $w_{ij}$ and piecewise-linear concave utilities $f^i_j$. Agent $j$ is **nonsatiated with respect to good $k$** if the last (infinite) segment of $f^j_k$ has positive slope, i.e. $\lim_{x\to\infty}f^j_k(x)=\infty$.
--
--   The **economy graph** of $M$ has a node for every agent and an arc $i\to j$ whenever some good $k$ has $w_{ik}>0$ and agent $j$ is nonsatiated with respect to $k$. Condition **(C')** asks that the economy graph be strongly connected:
--   $$\text{for all agents } i,j \text{ there is a directed path of positive length from } i \text{ to } j.$$
--
--   For a Fisher market with buyers $B$, condition **(C2)** (nonsatiation) asks that every buyer $i$ have a good $j$ such that the last segment of $f^i_j$ has positive slope.
--
--   These are the sufficient conditions for existence under which Theorem 6.1 places equilibrium computation in PPAD, and Theorem 7.1 shows PPAD-hardness for Fisher markets.
--
--   **Formalization Note** Strong connectivity is stated with paths of positive length (the transitive closure of the arc relation) between every ordered pair of agents, a pair $(i,i)$ included. For two or more agents this is ordinary strong connectivity. A single agent satisfies (C') only if it carries a loop, i.e. owns a good for which it is nonsatiated, so a satiated one-agent economy is not counted as strongly connected by a path of length zero. This is the reading under which the page's remarks hold for every number of agents: (C') implies (C2), and for a Fisher market written as an exchange market (C2) and (C') are equivalent (p. 10:10).
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, p. 10:10 (§6: (C2) nonsatiation, the economy graph of Maxfield [1997], condition (C'))

import Mathlib
import Definitions.Def_PLCMarkets_ExactCover_ADMarket
import Definitions.Def_PLCMarkets_Rationality_FisherMarket

namespace PLCMarkets.ExactCover.Supplement

open PLCMarkets.ExactCover

/-- The arcs of the **economy graph** of an Arrow–Debreu market (§6, p. 10:10, after Maxfield
1997): there is an arc `i → j` if some good `k` has `w_ik > 0` and agent `j` is nonsatiated with
respect to `k`, i.e. the last (infinite) segment of `f^j_k` has positive slope. -/
def EconArc {A G : Type} [Fintype A] [Fintype G] (M : ADMarket A G) (i j : A) : Prop :=
  ∃ k : G, 0 < M.endow i k ∧ 0 < (M.util j k).tail

/-- Condition **(C')** (§6, p. 10:10): the economy graph is strongly connected. Every agent reaches
every agent, itself included, along a path of positive length; for two or more agents this is
ordinary strong connectivity, and a single agent must carry a loop (own a good for which it is
nonsatiated), so a satiated one-agent economy does not satisfy (C'). -/
def ConditionCPrime {A G : Type} [Fintype A] [Fintype G] (M : ADMarket A G) : Prop :=
  ∀ i j : A, Relation.TransGen (EconArc M) i j

/-- Condition **(C2)** (nonsatiation, §6, p. 10:10) for a Fisher market: every buyer `i` has a good
`j` such that the last (infinite) segment of `f^i_j` has positive slope. -/
def FisherC2 {n g : ℕ} (M : PLCMarkets.Rationality.FisherMarket n g) : Prop :=
  ∀ i, ∃ j, 0 < (M.util i j).tail

end PLCMarkets.ExactCover.Supplement



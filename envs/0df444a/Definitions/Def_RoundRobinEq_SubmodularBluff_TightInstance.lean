-- Prove2me | Definitions.Def_RoundRobinEq_SubmodularBluff_TightInstance
-- name    : RoundRobinEq_SubmodularBluff_TightInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:17:23.53259+00:00
-- url     : https://prove2.me/theorems/0b97683f-8736-4817-9a92-d06f3d8bef3a
-- title:
--   pp. 13–14 — the two-agent tight instance of Theorem 3.7 (additive agent 1, OXS agent 2)
-- statement:
--   The instance showing that the factor $\tfrac12$ of Theorem 3.7 is tight (pp. 13–14) has two agents and goods $g_1,\dots,g_5$, with parameters $0<\varepsilon_1<\varepsilon_2<\varepsilon_3<1$.
--
--   1. Agent 1 is additive with singleton values
--   $$v_1(g_1)=2,\quad v_1(g_2)=1,\quad v_1(g_3)=1-\varepsilon_1,\quad v_1(g_4)=1-\varepsilon_2,\quad v_1(g_5)=1-\varepsilon_3.$$
--   2. Agent 2 is OXS: her value for a set is the weight of a maximum matching in the bipartite graph of p. 13, in which $g_1$ is joined to a first node with weight $2$, $g_2,g_4,g_5$ to a second node with weights $1,1-\varepsilon_2,1-\varepsilon_3$, and $g_3$ to a third node with weight $1-\varepsilon_1$. In closed form,
--   $$v_2(S)=2\,[g_1\in S]+(1-\varepsilon_1)[g_3\in S]+\max\{[g_2\in S],\,(1-\varepsilon_2)[g_4\in S],\,(1-\varepsilon_3)[g_5\in S]\}.$$
--   3. A sixth good $g_6$ has value $0$ for both agents and in every set; it makes the number of goods a multiple of the number of agents.
--
--   The file also records the paper's bluff order $g_1\succ g_2\succ g_3\succ g_4\succ g_5\,(\succ g_6)$ and agent 2's deviation $g_3\succ g_4\succ g_1\succ g_2\succ g_5\,(\succ g_6)$.
--
--   **Formalization Note.** Goods are `Fin 6` with $g_\ell$ encoded as $\ell-1$; agents 1, 2 are `0, 1 : Fin 2`. The closed formula for $v_2$ is our reading of the figure of p. 13, and it reproduces every value the text computes: $v_2(\{g_1,g_2\})=3$, $v_2(\{g_1,g_4,g_5\})=3-\varepsilon_2$, $v_2(\{g_2,g_4\})=1$, $v_2(\{g_1,g_3,g_5\})=4-\varepsilon_1-\varepsilon_3$, $v_2(\{g_3,g_5\})=2-\varepsilon_1-\varepsilon_3$, $v_2(\{g_3,g_4\})=2-\varepsilon_1-\varepsilon_2$. The dummy good $g_6$ is the paper's own device for its standing assumption $m=kn$ (p. 7). The page prints "$v_1(g_2)=1-\varepsilon_2$" for the fourth good; the value belongs to $g_4$.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, pp. 13–14, proof of Theorem 3.7 (tight instance and bipartite graph); p. 7 (dummy goods)

import Mathlib

namespace RoundRobinEq.SubmodularBluff

/-- The tight instance of Theorem 3.7 (pp. 13–14) with goods `g_1, …, g_6` encoded as
`0, …, 5 : Fin 6` (`g_6` is the dummy good of zero value for both agents added for `m = kn`)
and agents 1, 2 encoded as `0, 1 : Fin 2`.

* Agent 1 is additive: `v_1(g_1) = 2`, `v_1(g_2) = 1`, `v_1(g_3) = 1 - ε₁`, `v_1(g_4) = 1 - ε₂`,
  `v_1(g_5) = 1 - ε₃`, `v_1(g_6) = 0`.
* Agent 2 is the OXS function of the bipartite graph on p. 13 (`g_1` to node 1 with weight 2;
  `g_2, g_4, g_5` to node 2 with weights `1, 1 - ε₂, 1 - ε₃`; `g_3` to node 3 with weight
  `1 - ε₁`): `v_2(S) = 2·[g_1 ∈ S] + (1 - ε₁)·[g_3 ∈ S]
  + max{[g_2 ∈ S], (1 - ε₂)·[g_4 ∈ S], (1 - ε₃)·[g_5 ∈ S]}`. -/
def tightVal (ε₁ ε₂ ε₃ : ℝ) (i : Fin 2) (S : Finset (Fin 6)) : ℝ :=
  if i = 0 then
    (if (0 : Fin 6) ∈ S then 2 else 0) + (if (1 : Fin 6) ∈ S then 1 else 0) +
      (if (2 : Fin 6) ∈ S then 1 - ε₁ else 0) + (if (3 : Fin 6) ∈ S then 1 - ε₂ else 0) +
      (if (4 : Fin 6) ∈ S then 1 - ε₃ else 0)
  else
    (if (0 : Fin 6) ∈ S then 2 else 0) + (if (2 : Fin 6) ∈ S then 1 - ε₁ else 0) +
      max (if (1 : Fin 6) ∈ S then 1 else 0)
        (max (if (3 : Fin 6) ∈ S then 1 - ε₂ else 0) (if (4 : Fin 6) ∈ S then 1 - ε₃ else 0))

/-- The paper's (lexicographic) bluff order `g_1 > g_2 > g_3 > g_4 > g_5 (> g_6)` (p. 13). -/
def tightBluffOrder : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- Agent 2's deviation `g_3 > g_4 > g_1 > g_2 > g_5 (> g_6)` (p. 14). -/
def tightDeviation : List (Fin 6) := [2, 3, 0, 1, 4, 5]

end RoundRobinEq.SubmodularBluff



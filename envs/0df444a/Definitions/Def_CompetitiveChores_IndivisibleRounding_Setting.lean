-- Prove2me | Definitions.Def_CompetitiveChores_IndivisibleRounding_Setting
-- name    : CompetitiveChores_IndivisibleRounding_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:32.679988+00:00
-- url     : https://prove2.me/theorems/de7b9568-4548-47ea-b478-7b6f7550d097
-- title:
--   pp. 10–11 — chore division problem, feasible and competitive allocations, Pareto frontier, Nash social welfare
-- statement:
--   The chore division model of Brânzei and Sandomirskiy (§2, pp. 10–11).
--
--   There are $n$ agents and $m$ divisible chores; in Lean agents are indexed by $\mathrm{Fin}\,n$ and chores by $\mathrm{Fin}\,m$ (0-based). A **bundle** is a vector $x\in\mathbb R^m_{\ge 0}$, where $x_j$ is the amount of chore $j$; an **allocation** is a matrix $z=(z_{i,j})$, agent $i$ receiving the bundle $z_i$. It is **feasible** if $z\ge 0$ and every chore is fully distributed:
--
--   $$\sum_{i=1}^n z_{i,j}=1\quad\text{for each } j\in[m].$$
--
--   Agents have additive utilities given by a value matrix $v$: $u_i(x)=\sum_j v_{i,j}x_j$, and the **utility profile** of $z$ is $u(z)=(u_1(z_1),\dots,u_n(z_n))$. The set of feasible utility profiles is $\mathcal U(v)$. At prices $p\in\mathbb R^m$ a bundle costs $p(x)=\sum_j p_j x_j$.
--
--   **Definition 3 (competitive allocation).** A feasible allocation $z$ is competitive for budgets $b$ at prices $p\in\mathbb R^m_{<0}$ if for every agent $i$ the bundle $z_i$ is within her budget, $p(z_i)\le b_i$, and maximizes her utility among all bundles within her budget: $u_i(z_i)\ge u_i(x)$ for every $x\in\mathbb R^m_{\ge0}$ with $p(x)\le b_i$. It is competitive if such prices exist.
--
--   **Definition 5 (Pareto optimality).** A feasible $z$ is Pareto optimal if no feasible $z'$ gives every agent at least $u_i(z_i)$ and some agent strictly more. The **Pareto frontier** $\mathcal U^*(v)$ is the set of feasible utility profiles not weakly dominated by another feasible profile (equivalently, the utility profiles of Pareto optimal allocations).
--
--   The **Nash social welfare** of $z$ for budgets $b$ (p. 11) is $\prod_{i=1}^n |u_i(z_i)|^{|b_i|}$.
--
--   These objects underlie every statement of the mission.
--
--   **Formalization Note** The definitions carry no sign conditions: the hypotheses $v\in\mathbb R^{n\times m}_{<0}$ and $b\in\mathbb R^n_{<0}$ of a chore division problem (Definition 2) are stated in each theorem, because Theorem 35 applies Definition 3 to budgets $b'\le 0$. The budget clause $p(z_i)\le b_i$ is written out explicitly ("within her budget"). The Pareto frontier is encoded as the non-dominated feasible profiles. The real power $|u|^{|b|}$ is `Real.rpow` of a non-negative base.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, pp. 10–11, §2, Definitions 2, 3, 5; p. 11, §2.2 (Nash social welfare)

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting

namespace CompetitiveChores.IndivisibleRounding

variable {n m : ℕ}

/-- §2.2, p. 11: the Nash social welfare `∏_{i=1}^n |u_i(z_i)|^{|b_i|}` of the allocation `z` for the
budgets `b` (a real power of a non-negative base). -/
noncomputable def nashWelfare (v : Fin n → Fin m → ℝ) (b : Fin n → ℝ) (z : Fin n → Fin m → ℝ) : ℝ :=
  ∏ i, |CompetitiveChores.RichFamily.utilityProfile v z i| ^ |b i|

end CompetitiveChores.IndivisibleRounding



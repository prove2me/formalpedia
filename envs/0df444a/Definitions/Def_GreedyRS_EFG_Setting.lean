-- Prove2me | Definitions.Def_GreedyRS_EFG_Setting
-- name    : GreedyRS_EFG_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:56.609538+00:00
-- url     : https://prove2.me/theorems/0d23c838-2113-4537-8d36-f1683f397564
-- title:
--   §2, Procedure 2, §5.2–5.3 — normal observation array, explore-first greedy procedure, PCS, crossing times, C(x; n₀)
-- statement:
--   This file fixes the model and the objects of the explore-first greedy (EFG) analysis of Li, Fan and Hong.
--
--   **Alternatives and observations.** Alternatives are indexed by $i = 0, 1, 2, \dots$; problem $k$ uses alternatives $0, \dots, k-1$, and alternative $0$ plays the role of the paper's best alternative 1. An observation array $x_{ij}$ records the $(j+1)$-th observation of alternative $i$, and
--   $$\bar X_i(n) = \frac{1}{n}\sum_{j=0}^{n-1} x_{ij}$$
--   is the running average after $n \ge 1$ observations.
--
--   **The EFG procedure (Procedure 2).** Every alternative first receives $n_0$ observations. As long as the total number of observations is below the budget $B$, the alternative with the largest current running average $\bar X_i(n_i)$ receives one more observation; ties go to the smallest index. When the budget is exhausted, the alternative with the largest running average is selected (same tie rule). The loop runs exactly $B - n_0 k$ times (no greedy step when $B \le n_0 k$). The greedy procedure (Procedure 1) is the case $n_0 = 1$.
--
--   **The observation model (§2).** Observations $X_{ij}$ on a probability space $(\Omega, P)$ form a mutually independent array with $X_{ij} \sim N(\mu_i, \sigma_i^2)$. The **probability of correct selection** is
--   $$\mathrm{PCS} = P\{\text{the EFG procedure with } k, n_0, B \text{ selects alternative } 0\}.$$
--
--   **The standard normal running average (§5.2).** Let $Z_1, Z_2, \dots$ be iid $N(0,1)$, $\bar Z(n) = \frac1n\sum_{j=1}^n Z_j$, and
--   $$\tilde N(x; n_0) = \inf\{n \ge n_0 : \bar Z(n) < x\}, \qquad C(x; n_0) = \mathrm E\big[\tilde N(x;n_0)\big],$$
--   where the infimum is $+\infty$ when the running average never drops below $x$, so $C(x; n_0) \in [0, \infty]$. The auxiliary block crossing time is $\inf\{m \ge 1 : \bar Z(m n_0) < x\}$.
--
--   **Boundary crossing (§5.3).** For a path $y(n)$: "$\min_{n \ge n_0} y(n) > a$" means the path is bounded below from $n_0$ on and its infimum exceeds $a$; the boundary is $\min_{n\ge n_0} y(n)$; $\arg\min_{n \ge n_0} y(n)$ is the first index $\ge n_0$ attaining the minimum ($+\infty$ if none does); and $N(b; n_0) = \inf\{n \ge n_0 : y(n) < b\}$ ($+\infty$ if never).
--
--   These objects are shared by every statement of this mission.
--
--   **Formalization Note** Variances are carried as $v_i = \sigma_i^2 \in \mathbb R_{\ge 0}$; the standard normal sequence is the canonical infinite product law on $\mathbb R^{\mathbb N}$ (index $0$ is $Z_1$). Crossing times and argmins take values in $\mathbb N \cup \{\infty\}$, so a path that never crosses has crossing time $\infty$, not a junk $0$. Probabilities and $C(x;n_0)$ are extended nonnegative reals. The smallest-index tie rule only changes events of probability zero under the normal model.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 8, §2; p. 21, Procedure 2; p. 22, §5.2 (Ñ(x;n_0), C(x;n_0), (5.1)); p. 23, §5.3 (X̄_1^*(n_0), N_i(·;n_0), N_1^*(n_0))

import Mathlib
import Definitions.Def_GreedyRS_Greedy_Setting

namespace GreedyRS.EFG

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- `inf {m ≥ 1 : Z̄(m n0) < x}`, equal to `⊤` when no block average crosses. -/
noncomputable def blockCross (x : ℝ) (n0 : ℕ) (z : ℕ → ℝ) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : 1 ≤ m ∧ GreedyRS.Greedy.zbar z (m * n0) < x), (m : ℕ∞)

end GreedyRS.EFG



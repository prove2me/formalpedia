-- Prove2me | Definitions.Def_TwoEchelonVRP_zF
-- name    : TwoEchelonVRP_zF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:29:04.024798+00:00
-- url     : https://prove2.me/theorems/1a6fc423-036a-4c00-a9f2-3effdfff1f2c
-- title:
--   Formulation F of the 2E-CVRP and its optimal cost $z(F)$
-- statement:
--   A solution $(x, y, q)$ is **feasible for F** when it satisfies the linear constraints (2)–(8) (`LinearConstraints`) and the integrality constraints
--
--   $$
--   x_{kl} \in \{0,1\}\ (9), \qquad y_r \in \{0,1\}\ (10), \qquad q_{kr} \in \mathbb Z_+ \ \ (k \in R_r)\ (11).
--   $$
--
--   Its cost is the objective (1),
--
--   $$
--   \sum_{k \in N_S} \sum_{l \in \mathcal R_k} c_{kl} x_{kl} + \sum_{r \in \mathcal M} g_r y_r ,
--   $$
--
--   and the optimal 2E-CVRP cost $z(F)$ is the minimum of (1) over the feasible solutions.
--
--   **Formalization Note** Variables are real-valued with integrality as predicates ($q_{kr} \in \mathbb Z_+$ is "$q_{kr} = n$ for some natural number $n$"). $z(F)$ is the infimum in the extended reals $[-\infty, +\infty]$ of the objective values of the feasible solutions; it is $+\infty$ when F is infeasible, and a real minimum otherwise (the feasible set is finite). The module declares `FFeasible`, `objF` and `zF`.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §2.1, formulation (F), (1)–(11), p. 300

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance
import Definitions.Def_TwoEchelonVRP_Route2
import Definitions.Def_TwoEchelonVRP_Route1
import Definitions.Def_TwoEchelonVRP_LinearConstraints

namespace TwoEchelonVRP

/-- **Feasible solutions of formulation F** of the 2E-CVRP.
Baldacci et al., *An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem*,
Operations Research 61(2) (2013) 298–314, §2.1, formulation (F), constraints (2)–(11), p. 300:
the linear constraints (2)–(8) (`LinearConstraints`) and
(9) `x_kl ∈ {0, 1}`, (10) `y_r ∈ {0, 1}`, (11) `q_kr ∈ ℤ₊` for `k ∈ R_r`.

**Formalization Note.** Variables are real-valued and integrality is a predicate: `q_kr ∈ ℤ₊` is
`∃ n : ℕ, q_kr = n`. -/
def FFeasible {ns nc : ℕ} (I : Instance ns nc) (x : Fin ns → Route2 I → ℝ)
    (y : Route1 I → ℝ) (qd : Route1 I → Fin ns → ℝ) : Prop :=
  LinearConstraints I x y qd ∧
    (∀ k l, x k l = 0 ∨ x k l = 1) ∧
    (∀ r, y r = 0 ∨ y r = 1) ∧
    (∀ r, ∀ k ∈ satSet r, ∃ n : ℕ, qd r k = n)

/-- **Objective (1) of formulation F**: `Σ_{k ∈ N_S} Σ_{l ∈ 𝓡_k} c_kl x_kl + Σ_{r ∈ 𝓜} g_r y_r`
(Baldacci et al., Operations Research 61(2) (2013), §2.1, (1), p. 300). The vehicle fixed costs and
handling costs are inside `c_kl` and `g_r` (p. 299). -/
noncomputable def objF {ns nc : ℕ} (I : Instance ns nc) (x : Fin ns → Route2 I → ℝ)
    (y : Route1 I → ℝ) : ℝ :=
  ∑ k, ∑ l, cost2 I k l * x k l + ∑ r, cost1 I r * y r

/-- **The optimal 2E-CVRP cost** `z(F)`.
Baldacci et al., Operations Research 61(2) (2013), §2.1, (F)–(1), p. 300:
`z(F) = min Σ_k Σ_{l ∈ 𝓡_k} c_kl x_kl + Σ_r g_r y_r` subject to (2)–(11).

**Formalization Note.** `z(F)` is the infimum in `EReal` of the objective values of the feasible
solutions; it is `⊤` (`+∞`) when F has no feasible solution. Its feasible set is finite, so when it is
nonempty the infimum is a minimum and is a real number. -/
noncomputable def zF {ns nc : ℕ} (I : Instance ns nc) : EReal :=
  sInf ((fun v : ℝ => (v : EReal)) ''
    {v | ∃ x y qd, FFeasible I x y qd ∧ v = objF I x y})

end TwoEchelonVRP



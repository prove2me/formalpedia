-- Prove2me | Definitions.Def_FairExplore_Program
-- name    : FairExplore_Program
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:24.88427+00:00
-- url     : https://prove2.me/theorems/b6259e2b-d83e-434c-89f3-83c6e9d8210a
-- title:
--   Program (13): Nash welfare value $Y^*(\mathcal I)$ and its minimum-norm optimal solution
-- statement:
--   For a parameter vector $\theta$ (the true one, or an estimate $\hat\theta_t$), program (13) is
--   $$Y^*=\max_{q\ge0}\ \sum_{g\in G}\log\Big(\sum_{a\in\mathcal A^g_{\mathrm{sub}}}\Delta^g(a)\big(J^g(a)-q^g(a)J(a)\big)\Big)$$
--   subject to $\sum_{g}q^g(a)=1$ for $a\in\mathcal A_{\mathrm{sub}}$ and $q^g(a)=0$ for $a\notin\mathcal A_{\mathrm{sub}}\cap\mathcal A^g$, with $\log u=-\infty$ for $u\le0$; all quantities are computed from $\theta$.
--
--   1. **Value.** $Y^*(\mathcal I)$ is the supremum of the objective over the feasible set, an extended real number.
--   2. **Optimal solutions.** $q$ is optimal if it is feasible and its objective is at least that of every feasible point.
--   3. **Minimum-norm solution.** $q^*$ (and PF-UCB's $\hat q_t$ at $\theta=\hat\theta_t$) is an optimal solution with the smallest Euclidean norm $\sum_{g,a}q^g(a)^2$ among all optimal solutions.
--
--   $Y^*(\mathcal I)$ is the upper bound on the Nash social welfare of every consistent policy (Theorem 2) and the value PF-UCB attains (Theorem 3); $q^g_*(a)$ is the share of the exploration of arm $a$ that group $g$ bears.
--
--   **Formalization Note** The objective is `EReal`-valued, with $\log u=\bot$ for $u\le0$. The paper's max is written as `sSup` of the objective over the feasible set. The minimum-norm solution is chosen with `Classical.choose` (and $0$ if none exists); the milestone `min_norm_solution_exists_unique` states that it exists and is unique for every parameter vector, so the choice is the paper's object. The printed "$\mathcal A_g$" in the last constraint is read as $\mathcal A^g$. The parameter is any real vector, since estimates may leave $(0,1)$ and may tie.
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, (13), p.13; P(θ̂_t), p.14; (14), p.15

import Mathlib
import Definitions.Def_FairExplore_KArmed

namespace FairExplore

variable {γ α : Type*} [Fintype γ] [Fintype α] [DecidableEq α]

/-- `log u` with the paper's convention `log u ≜ −∞` for `u ≤ 0` ((4), p.9; p.7). -/
noncomputable def elog (x : ℝ) : EReal :=
  if 0 < x then ((Real.log x : ℝ) : EReal) else ⊥

/-- The feasible set of program (13) (p.13), and of `P(θ̂_t)` (p.14), at a parameter vector `θ`
(the true `θ`, or an estimate): `q ≥ 0`, `∑_g q^g(a) = 1` for `a ∈ A_sub`, and `q^g(a) = 0` for
`a ∉ A_sub ∩ A^g`.

**Formalization Note** `q : γ → α → ℝ` is indexed by all pairs; the last constraint forces
`q^g(a) = 0` off `A^g`, so this is the paper's `(q^g(a))_{g ∈ G, a ∈ A^g}`. The printed `A_g` in
the last constraint is read as `A^g`. `θ` is any real vector, since the estimate `θ̂_t` may leave
`(0,1)` and may have ties. -/
def Feasible (A : γ → Finset α) (θ : α → ℝ) (q : γ → α → ℝ) : Prop :=
  (∀ g a, 0 ≤ q g a) ∧ (∀ a ∈ subAll A θ, ∑ g, q g a = 1) ∧
    (∀ g a, ¬ (a ∈ subAll A θ ∧ a ∈ A g) → q g a = 0)

/-- The objective of (13) (p.13): `∑_g log(∑_{a ∈ A^g_sub} ∆^g(a)(J^g(a) − q^g(a)J(a)))`, with
`log u = −∞` for `u ≤ 0`, in `EReal`. -/
noncomputable def objective (A : γ → Finset α) (θ : α → ℝ) (q : γ → α → ℝ) : EReal :=
  ∑ g, elog (∑ a ∈ subG A θ g, gap A θ g a * (Jg A θ g a - q g a * Jmax A θ a))

/-- `Y*(I)`, the optimal value of program (13) (p.13), at the parameter `θ`.

**Formalization Note** The paper's `max` is written as the supremum in `EReal` of the objective
over the feasible set; it equals the maximum whenever the maximum is attained (milestone
`min_norm_solution_exists_unique` shows it is). -/
noncomputable def Ystar (A : γ → Finset α) (θ : α → ℝ) : EReal :=
  sSup (objective A θ '' {q | Feasible A θ q})

/-- `q` is an optimal solution of (13) (or of `P(θ̂)`) at the parameter `θ`. -/
def IsOpt (A : γ → Finset α) (θ : α → ℝ) (q : γ → α → ℝ) : Prop :=
  Feasible A θ q ∧ ∀ q', Feasible A θ q' → objective A θ q' ≤ objective A θ q

/-- `q` is an optimal solution of (13) with the smallest Euclidean norm among all optimal solutions
(p.14: "the solution to the following optimization problem with the smallest Euclidean norm"; p.15:
"q* is the optimal solution to (13) with the smallest Euclidean norm"). -/
def IsMinNormOpt (A : γ → Finset α) (θ : α → ℝ) (q : γ → α → ℝ) : Prop :=
  IsOpt A θ q ∧ ∀ q', IsOpt A θ q' → ∑ g, ∑ a, q g a ^ 2 ≤ ∑ g, ∑ a, q' g a ^ 2

open Classical in
/-- The minimum-norm optimal solution of (13) at the parameter `θ`: `q*` at the true parameter
(p.15), and PF-UCB's `q̂_t` at `θ = θ̂_t` (p.14).

**Formalization Note** Chosen by `Classical.choose` when a minimum-norm optimal solution exists,
and `0` otherwise; milestone `min_norm_solution_exists_unique` shows that it exists and is unique for
every `θ` (when every arm belongs to some group), so this is the paper's object. -/
noncomputable def qhat (A : γ → Finset α) (θ : α → ℝ) : γ → α → ℝ :=
  if h : ∃ q, IsMinNormOpt A θ q then Classical.choose h else 0

end FairExplore



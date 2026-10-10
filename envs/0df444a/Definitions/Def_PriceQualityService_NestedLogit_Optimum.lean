-- Prove2me | Definitions.Def_PriceQualityService_NestedLogit_Optimum
-- name    : PriceQualityService_NestedLogit_Optimum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:28:13.304429+00:00
-- url     : https://prove2.me/theorems/d4837985-d8ff-490f-885c-f1dc01e68c3a
-- title:
--   Theorem 4, p. 19 — the optimal qualities $q^\dagger_{xi}$, the prices $p^\dagger_{xi}$ and the right-hand side of the fixed-point equation for $r^\dagger$
-- statement:
--   This file defines the closed-form objects that appear in Theorem 4.
--
--   With $u_{xj}(\mathbf q)=\alpha_{xj}q_{xj}-c_{xj}q_{xj}^2-t_x(a_{xj}-b_{xj}q_{xj})+t_xs_{xj}$ as in the markup-problem file, define, for a quality vector $\mathbf q$ and a real number $r$,
--   $$
--   F(\mathbf q,r)=\sum_{x\in\{s,l\}}\mu_1\Bigl(\sum_{j=1}^{m_x}\exp\bigl(u_{xj}(\mathbf q)-r-\mu_1\bigr)\Bigr)^{1/\mu_1},
--   $$
--   the right-hand side of (EC.7), (EC.8) and of the equation of Theorem 4(b). Define the quality vector $\mathbf q^\dagger$ and, for each real $r$, the price vector $\mathbf p^\dagger(r)$ by
--   $$
--   q^\dagger_{xi}=\frac{\alpha_{xi}+t_xb_{xi}}{2c_{xi}},\qquad
--   p^\dagger_{xi}(r)=\mu_1+r+c_{xi}(q^\dagger_{xi})^2+t_x\bigl(a_{xi}-b_{xi}q^\dagger_{xi}\bigr).
--   $$
--
--   Theorem 4 asserts that $\mathbf q^\dagger$ and $\mathbf p^\dagger(r^\dagger)$ are the optimal decisions, where $r^\dagger$ is the unique solution of $r=F(\mathbf q^\dagger,r)$. These definitions do not assert any optimality; they only name the formulas.
--
--   **Formalization Note.** $\mathbf p^\dagger$ takes $r$ as an argument, so the optimum is not defined by the paper's formula: the theorem has to identify the right $r$ and prove optimality. $q^\dagger_{xi}$ divides by $c_{xi}$, and every theorem assumes $c_{xi}>0$.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 19, Theorem 4; Online Supplement p. 6 (PDF p. 39), (EC.7), (EC.8)

import Mathlib
import Definitions.Def_PriceQualityService_NestedLogit_MarkupProblem

namespace PriceQualityService.NestedLogit

/-- The right-hand side of (EC.7)/(EC.8) and of the equation of Theorem 4(b) (p. 19; Online
Supplement p. 6), as a function of the quality vector `q` and of `r`:
`∑_{x∈{s,l}} μ₁ (∑_{j=1}^{m_x} exp(α_xj q_xj − c_xj q_xj² − t_x (a_xj − b_xj q_xj) + t_x s_xj − r − μ₁))^{1/μ₁}`.
The power is `Real.rpow` of a nonnegative base; an empty nest contributes `μ₁ · 0 ^ (1/μ₁) = 0`. -/
noncomputable def fixedPointRHS (M : Model) (q : Vec M) (r : ℝ) : ℝ :=
  ∑ x, M.μ₁ * (∑ j, Real.exp (netUtility M q x j - r - M.μ₁)) ^ (1 / M.μ₁)

/-- The quality vector of Theorem 4(a), p. 19: `q†_xi = (α_xi + t_x b_xi) / (2 c_xi)`. -/
noncomputable def qDagger (M : Model) : Vec M :=
  fun x i => (M.α x i + M.t x * M.b x i) / (2 * M.c x i)

/-- The price vector of Theorem 4(b), p. 19, for a given value `r` of the profit:
`p_xi = μ₁ + r + c_xi q†_xi² + t_x (a_xi − b_xi q†_xi)`. Theorem 4 takes `r = r†`, the root of
`r = fixedPointRHS M (qDagger M) r`; this definition does not fix `r`. -/
noncomputable def pDagger (M : Model) (r : ℝ) : Vec M :=
  fun x i => M.μ₁ + r + M.c x i * qDagger M x i ^ 2 + M.t x * (M.a x i - M.b x i * qDagger M x i)

end PriceQualityService.NestedLogit



-- Prove2me | Definitions.Def_MPBSelect_Problem_dGdOwn
-- name    : MPBSelect_Problem_dGdOwn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:44.092175+00:00
-- url     : https://prove2.me/theorems/f3da9a70-ed49-424c-ac71-0ff1eed04172
-- title:
--   Closed forms of $\partial G_i(\theta_b)/\partial\alpha_i(\theta_b)$ and $\partial G_i(\theta_b)/\partial\alpha_{i^b}(\theta_b)$
-- statement:
--   For an allocation $\boldsymbol\alpha$ and a pair $(i,\theta_b)$, write
--   $$
--   S_i(\theta_b)=\frac{\lambda_i^2(\theta_b)}{\alpha_i(\theta_b)}+\frac{\lambda_{i^b}^2(\theta_b)}{\alpha_{i^b}(\theta_b)}
--   $$
--   for the quantity in the denominator of $G_i(\theta_b)$, and define
--   $$
--   \partial_iG_i(\theta_b)=G_i(\theta_b)\,\frac{\lambda_i^2(\theta_b)/\alpha_i^2(\theta_b)}{S_i(\theta_b)},\qquad \partial_{i^b}G_i(\theta_b)=G_i(\theta_b)\,\frac{\lambda_{i^b}^2(\theta_b)/\alpha_{i^b}^2(\theta_b)}{S_i(\theta_b)} .
--   $$
--   When $i\ne i^b$ and both ratios are positive, these are the partial derivatives of $G_i(\theta_b)$ in $\alpha_i(\theta_b)$ and in $\alpha_{i^b}(\theta_b)$ (milestone "partial derivatives of the pairwise rate"). They enter the KKT conditions (EC.19)–(EC.20).
--
--   **Formalization Note** These are closed-form expressions, meaningful when both ratios are positive. The paper prints the denominator of $\partial_iG_i$ with $\alpha^2$ in place of $\alpha$; the formula here is the corrected one.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, proof of Theorem 3, (EC.19)–(EC.22) and the line below (EC.22), pp.ec9–ec10

import Mathlib
import Definitions.Def_MPBSelect_Problem
import Definitions.Def_MPBSelect_Problem_G

namespace MPBSelect

/-- The quantity `S_i(θ_b) = λ²_i(θ_b)/α_i(θ_b) + λ²_{i^b}(θ_b)/α_{i^b}(θ_b)` inside the
denominator of `G_i(θ_b)` (p.16), so that `G = (y_i − y_{i^b})² / (2 S)` when both ratios are
positive. -/
noncomputable def Problem.rateDenom {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ) (i : Fin k)
    (b : Fin B) : ℝ :=
  P.lam i b ^ 2 / α i b + P.lam (P.ib b) b ^ 2 / α (P.ib b) b

/-- **Partial derivative `∂G_i(θ_b)/∂α_i(θ_b)`, explicit form.**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, proof of Theorem 3,
line below (EC.22), p.ec10 (corrected denominator):
`∂Gi(θb)/∂αi(θb) = Gi(θb) · (λ²i(θb)/α²i(θb)) / (λ²i(θb)/αi(θb) + λ²_{i^b}(θb)/α_{i^b}(θb))`.

Used in the KKT conditions (EC.19) and in the derivative identity of the proof.

**Formalization Note** This is the closed-form expression, meaningful when `α_i(θ_b) > 0` and
`α_{i^b}(θ_b) > 0`; that it is the derivative is the milestone `theorem_3_partial_derivatives`.
The page prints the denominator with `α²` in place of `α`; see that milestone. -/
noncomputable def Problem.dGdOwn {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ) (i : Fin k)
    (b : Fin B) : ℝ :=
  P.G α i b * (P.lam i b ^ 2 / α i b ^ 2) / P.rateDenom α i b

/-- **Partial derivative `∂G_i(θ_b)/∂α_{i^b}(θ_b)`, explicit form.**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, proof of Theorem 3,
(EC.20) and (EC.22), pp.ec9–ec10:
`∂Gi(θb)/∂α_{i^b}(θb) = Gi(θb) · (λ²_{i^b}(θb)/α²_{i^b}(θb)) / (λ²i(θb)/αi(θb) + λ²_{i^b}(θb)/α_{i^b}(θb))`.

**Formalization Note** Closed form, meaningful when both ratios are positive. -/
noncomputable def Problem.dGdOpt {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ) (i : Fin k)
    (b : Fin B) : ℝ :=
  P.G α i b * (P.lam (P.ib b) b ^ 2 / α (P.ib b) b ^ 2) / P.rateDenom α i b

end MPBSelect



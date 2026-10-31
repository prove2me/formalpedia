-- Prove2me | Definitions.Def_MPBSelect_Problem_G
-- name    : MPBSelect_Problem_G
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:26:38.674935+00:00
-- url     : https://prove2.me/theorems/032b0bda-bba8-44df-b3f5-9aa79db4c28e
-- title:
--   The pairwise rate $G_i(\theta_b)$
-- statement:
--   For an allocation $\boldsymbol\alpha$ and a pair $(i,\theta_b)$ with $i\ne i^b$, the **pairwise rate** is
--   $$
--   G_i(\theta_b)=\begin{cases}\dfrac{(y_i(\theta_b)-y_{i^b}(\theta_b))^2}{2\big(\lambda_i^2(\theta_b)/\alpha_i(\theta_b)+\lambda_{i^b}^2(\theta_b)/\alpha_{i^b}(\theta_b)\big)}, & \alpha_i(\theta_b)>0\text{ and }\alpha_{i^b}(\theta_b)>0,\\[6pt] 0, & \text{otherwise.}\end{cases}
--   $$
--   It is the large-deviations rate at which $i$ falsely beats $i^b$ at $\theta_b$ (Glynn and Juneja 2004), and the paper uses it as a lower bound of the exact rate $\widetilde G_i(\theta_b)$ to obtain the relaxed problem (20).
--
--   **Formalization Note** The "otherwise $0$" branch is an explicit `if`. The page writes $\lambda^2_{i^b}(\theta)$ in the second denominator term; this is read as $\lambda^2_{i^b}(\theta_b)$. The formula is defined for every pair; only pairs with $i\ne i^b$ are used.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, §4.2, p.16, definition of G_i(θ_b)

import Mathlib
import Definitions.Def_MPBSelect_Problem

namespace MPBSelect

/-- **Pairwise rate `G_i(θ_b)`.**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, §4.2, p.16:
`Gi(θb) := (yi(θb) − y_{i^b}(θb))² / (2 (λ²i(θb)/αi(θb) + λ²_{i^b}(θb)/α_{i^b}(θb)))` if
`αi(θb) > 0 and α_{i^b}(θb) > 0`, and `Gi(θb) := 0` otherwise.

Here `α : Fin k → Fin B → ℝ` is a static sampling-ratio vector, `α i b = α_i(θ_b)` (p.11).

**Formalization Note** The `otherwise 0` branch is written as an explicit `if` (Lean's
`x / 0 = 0` would not give it). The page prints `λ²_{i^b}(θ)` in the second denominator term;
this is read as `λ²_{i^b}(θ_b)`. `lam` is the standard deviation, so `lam ^ 2` is the variance. -/
noncomputable def Problem.G {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ) (i : Fin k) (b : Fin B) : ℝ :=
  if 0 < α i b ∧ 0 < α (P.ib b) b then
    (P.y i b - P.y (P.ib b) b) ^ 2 /
      (2 * (P.lam i b ^ 2 / α i b + P.lam (P.ib b) b ^ 2 / α (P.ib b) b))
  else 0

end MPBSelect



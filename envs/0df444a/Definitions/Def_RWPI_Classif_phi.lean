-- Prove2me | Definitions.Def_RWPI_Classif_phi
-- name    : RWPI_Classif_phi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:32:54.292934+00:00
-- url     : https://prove2.me/theorems/7804802f-6b47-49d4-8877-0c61f3200877
-- title:
--   The dual integrand φ_γ of the optimal-transport DRO problem (Eq. (11))
-- statement:
--   Let $Z$ be a set, let $c : Z \times Z \to [0,\infty]$ be a cost function with $c(z,z) = 0$ for every $z$, and let $l : Z \to [0,\infty)$ be a nonnegative loss. For $\gamma \ge 0$ and a point $z_0 \in Z$, the **dual integrand** of Eq. (11) is
--
--   $$\varphi_\gamma(z_0) = \sup_{z \in Z}\big\{ l(z) - \gamma\, c(z, z_0) \big\},$$
--
--   with the convention $\infty \cdot 0 = 0$. Its value lies in $[0,\infty]$; it is at least $l(z_0)$.
--
--   It is the integrand of the one-dimensional dual problem in the strong duality result (Proposition 1), where $Z = \mathbb R^d \times \mathbb R$ and $z_0$ runs over the training points $(X_i, Y_i)$; for the logistic and hinge losses under the label-preserving cost $N_q$ it is computed in closed form in the proof of Theorem 2.
--
--   **Formalization Note** The dual integrand is computed in `ℝ≥0∞` as `⨆ z, (ENNReal.ofReal (l z) − ENNReal.ofReal γ * c z z₀)` with truncated subtraction; for a nonnegative loss and a cost vanishing on the diagonal this is exactly the paper's $\varphi_\gamma$, because the term at $z = z_0$ dominates every truncated term, and `0 * ⊤ = 0` is the paper's convention. The transport cost $D_c$ of Eq. (7) and the worst-case expected loss are the shared definitions `RWPI.SqrtLasso.transportCost` and `RWPI.SqrtLasso.worstCase`.
-- source:
--   Blanchet, Kang & Murthy, Robust Wasserstein Profile Inference and Applications to Machine Learning, arXiv:1610.05627v4, p. 10, Eq. (11)

import Mathlib

open scoped ENNReal

namespace RWPI.Classif

/-- Eq. (11), p. 10: `φ_γ(z₀) = sup_{z} { l(z) − γ c(z, z₀) }`, the supremum over the whole space,
computed in `[0, ∞]` for a loss `l ≥ 0`. Truncated subtraction is harmless because the term at
`z = z₀` (where `c z₀ z₀ = 0`) already dominates every truncated term, and `0 * ⊤ = 0` is the
paper's convention `∞ × 0 = 0`. -/
noncomputable def phi {Z : Type*} (c : Z → Z → ℝ≥0∞) (l : Z → ℝ) (γ : ℝ) (z₀ : Z) : ℝ≥0∞ :=
  ⨆ z : Z, (ENNReal.ofReal (l z) - ENNReal.ofReal γ * c z z₀)

end RWPI.Classif



-- Prove2me | Definitions.Def_FTPLLinBandit_fisherOp
-- name    : FTPLLinBandit_fisherOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:58.827563+00:00
-- url     : https://prove2.me/theorems/4ffd32c2-8b92-4a85-be07-6d5da162de09
-- title:
--   Operator norm $\|\mathcal I^v(\rho)\|_{\mathrm{op}}$
-- statement:
--   For a density $\rho$ and a shift $v$, the **operator norm** of the positive semidefinite matrix $\mathcal I^v(\rho)$ is
--   $$\|\mathcal I^v(\rho)\|_{\mathrm{op}}=\sup_{\|u\|_2\le1}u^\top\mathcal I^v(\rho)u\in[0,\infty].$$
--   Lemma 5 uses $\lambda\|\mathcal I^v_1\|_{\mathrm{op}}$, and Table 2 bounds it by a universal constant for the three initializers when $\|v\|_2\le\sqrt\lambda/8$.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Lemma 5, Eq. (13), p.11; proof of Lemma 5, p.29

import Mathlib
import Definitions.Def_FTPLLinBandit_fisherQ

open scoped ENNReal

namespace FTPLLinBandit

/-- **The operator norm `‖I^v(ρ)‖_op` of the shifted Fisher-information matrix.** Wei,
arXiv:2610.17818, Lemma 5, Eq. (13), p.11 (`λ‖I^v_1‖_op`); proof of Lemma 5, p.29 ("≤ ‖θ‖²₂
sup_{‖u‖₂≤1} ∫ (⟨u, ∇ρ₁(z − v)⟩)²/ρ₁(z) dz").

`fisherOp ρ v = sup_{‖u‖ ≤ 1} uᵀ I^v(ρ) u ∈ [0, ∞]`.

**Formalization Note.** `I^v(ρ)` is positive semidefinite, so its operator norm is the supremum of
its quadratic form over the unit ball; the supremum is taken in `[0, ∞]`, where it may be `∞`. -/
noncomputable def fisherOp {d : ℕ} (ρ : EuclideanSpace ℝ (Fin d) → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ⨆ u : EuclideanSpace ℝ (Fin d), ⨆ (_ : ‖u‖ ≤ 1), fisherQ ρ v u

end FTPLLinBandit



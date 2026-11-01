-- Prove2me | Definitions.Def_ConicBlackwell_weightedRegret
-- name    : ConicBlackwell_weightedRegret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:26.524689+00:00
-- url     : https://prove2.me/theorems/07c92eb0-ea87-4b50-8fd8-7e10570e8684
-- title:
--   $\theta$-weighted regret $\sum_{t=1}^T\theta_t\langle f_t,x_t\rangle-\min_{x\in\mathcal X}\sum_{t=1}^T\theta_t\langle f_t,x\rangle$
-- statement:
--   For a decision set $\mathcal X\subset\mathbb R^n$, decision weights $(\theta_t)_{t\ge1}$, losses $(f_t)_{t\ge1}$, decisions $(x_t)_{t\ge1}$ and a horizon $T$, the **$\theta$-weighted regret** is
--
--   $$
--   \sum_{t=1}^T\theta_t\langle f_t,x_t\rangle-\min_{x\in\mathcal X}\sum_{t=1}^T\theta_t\langle f_t,x\rangle .
--   $$
--
--   **Formalization Note** It is the published linear regret `ApproachRegret.Calibration.linRegret` against the weighted losses $\theta_tf_t$ (because $\langle\theta_tf_t,x\rangle=\theta_t\langle f_t,x\rangle$). The minimum is the infimum (`sInf`) of the image of $\mathcal X$; on a nonempty compact $\mathcal X$ it is attained, so it is the paper's minimum. Rounds are $t\in\{1,\dots,T\}$.
-- source:
--   Grand-Clément & Kroer, Solving Optimization Problems with Blackwell Approachability, arXiv:2202.12277v1 (https://arxiv.org/abs/2202.12277v1), Theorem 3.3, p.8 (numerator of the left-hand side)

import Mathlib
import Definitions.Def_ApproachRegret_Calibration_Game
open scoped RealInnerProductSpace
open ApproachRegret.ToOLO

namespace ConicBlackwell

/-- **The θ-weighted regret** `Σ_{t=1}^T θ_t⟨f_t, x_t⟩ − min_{x∈X} Σ_{t=1}^T θ_t⟨f_t, x⟩`.
Grand-Clément & Kroer, *Solving Optimization Problems with Blackwell Approachability*, arXiv:2202.12277v1, Theorem 3.3, p.8 (numerator of the left-hand side).

Formalization Note: the minimum over `X` is `sInf` of the image of `X`; on a nonempty compact `X`
the continuous linear function attains its infimum, so this is the paper's min.  Rounds are
`t ∈ Finset.Icc 1 T`.  It is the published linear regret `ApproachRegret.Calibration.linRegret`
against the weighted losses `θ_t f_t`, since `⟨θ_t f_t, x⟩ = θ_t ⟨f_t, x⟩`. -/
noncomputable def weightedRegret {n : ℕ} (X : Set (E n)) (θ : ℕ → ℝ) (f x : ℕ → E n)
    (T : ℕ) : ℝ :=
  ApproachRegret.Calibration.linRegret X T (fun t => θ t • f t) x

end ConicBlackwell



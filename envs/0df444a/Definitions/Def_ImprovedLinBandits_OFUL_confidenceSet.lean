-- Prove2me | Definitions.Def_ImprovedLinBandits_OFUL_confidenceSet
-- name    : ImprovedLinBandits_OFUL_confidenceSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:18:55.455102+00:00
-- url     : https://prove2.me/theorems/0a3f251c-7dbf-497b-b6c1-98834aa56f01
-- title:
--   Confidence ellipsoid $C_t$ of Theorem 2
-- statement:
--   Fix $d \ge 0$, a noise level $R \ge 0$, reals $S$, $\lambda$ and $\delta$, actions $X_1, X_2, \dots \in \mathbb R^d$ and rewards $Y_1, Y_2, \dots \in \mathbb R$. For $t \ge 0$ let
--
--   1. $\overline V_t = \lambda I + \sum_{s=1}^t X_s X_s^\top$ be the regularized design matrix;
--   2. $\widehat\theta_t = \overline V_t^{-1} \sum_{s=1}^t Y_s X_s$ be the $\ell^2$-regularized least-squares estimate, i.e. $\widehat\theta_t = (\mathbf X_{1:t}^\top \mathbf X_{1:t} + \lambda I)^{-1} \mathbf X_{1:t}^\top \mathbf Y_{1:t}$ (Eq. (1) of the paper);
--   3. $\|v\|_A = \sqrt{v^\top A v}$.
--
--   The **confidence radius** is
--
--   $$\beta_t = R\sqrt{2\log\left(\frac{\det(\overline V_t)^{1/2}\det(\lambda I)^{-1/2}}{\delta}\right)} + \lambda^{1/2} S ,$$
--
--   and the **confidence ellipsoid** is
--
--   $$C_t = \left\{\theta \in \mathbb R^d : \left\|\widehat\theta_t - \theta\right\|_{\overline V_t} \le \beta_t\right\}.$$
--
--   This is the set of Theorem 2; it depends only on the first $t$ rounds, and the OFUL algorithm uses $C_{t-1}$ at round $t$. For $\lambda > 0$ and $S \ge 0$ it is a nonempty (it contains $\widehat\theta_t$) compact ellipsoid.
--
--   **Formalization Note** $\overline V_t$ and $\widehat\theta_t$ are the platform definitions `BanditAlgorithm.regularizedDesignMatrix` and `BanditAlgorithm.regularizedLeastSquares`. $\det(\cdot)^{1/2}$ is `Real.sqrt` of the determinant, and $\det(\lambda I)$ is written literally. For $\lambda > 0$ both determinants are positive, so the logarithm's argument is positive; for $\delta > 1$ it can be below $1$, and then Lean's square root of the negative radicand is $0$. The theorems that use $C_t$ are trivial for $\delta \ge 1$.
-- source:
--   Abbasi-Yadkori, Pál, Szepesvári, Improved Algorithms for Linear Stochastic Bandits, NIPS 2011, p. 4, Theorem 2 (the set $C_t$) and §4 eq. (1)

import Mathlib
import Definitions.Def_SelfNormalizedProcess

open Matrix NNReal

namespace ImprovedLinBandits.OFUL

/-- The radius of the confidence ellipsoid `C_t` of Theorem 2 (Abbasi-Yadkori, Pál, Szepesvári,
NIPS 2011, p. 4):
`R √(2 log(det(V̄_t)^{1/2} det(λI)^{-1/2} / δ)) + λ^{1/2} S`,
where `V̄_t = λI + ∑_{s=1}^t X_s X_sᵀ` is `BanditAlgorithm.regularizedDesignMatrix d lam X t ω`.
For `λ > 0` both determinants are positive. For `δ > 1` the logarithm can be negative, and then
Lean's `Real.sqrt` returns `0`; the theorems using this set are trivial for `δ ≥ 1`. -/
noncomputable def confidenceRadius {Ω : Type*} (d : ℕ) (R : ℝ≥0) (S lam δ : ℝ)
    (X : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (R : ℝ) * Real.sqrt (2 * Real.log
      (Real.sqrt (BanditAlgorithm.regularizedDesignMatrix d lam X t ω).det *
        (Real.sqrt (lam • (1 : Matrix (Fin d) (Fin d) ℝ)).det)⁻¹ / δ))
    + Real.sqrt lam * S

/-- The confidence ellipsoid `C_t` of Theorem 2 (Abbasi-Yadkori, Pál, Szepesvári, NIPS 2011,
p. 4): the set of `θ ∈ ℝ^d` with `‖θ̂_t - θ‖_{V̄_t} ≤ confidenceRadius`, where `θ̂_t` is the
`λ`-regularized least-squares estimate of Eq. (1) computed from the actions `X 1, …, X t` and
rewards `Y 1, …, Y t` (`BanditAlgorithm.regularizedLeastSquares d lam X Y t ω`), and
`‖v‖_A = √(vᵀ A v)`. -/
noncomputable def confidenceSet {Ω : Type*} (d : ℕ) (R : ℝ≥0) (S lam δ : ℝ)
    (X : ℕ → Ω → Fin d → ℝ) (Y : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Set (Fin d → ℝ) :=
  {θ | Real.sqrt ((BanditAlgorithm.regularizedLeastSquares d lam X Y t ω - θ) ⬝ᵥ
        BanditAlgorithm.regularizedDesignMatrix d lam X t ω *ᵥ
          (BanditAlgorithm.regularizedLeastSquares d lam X Y t ω - θ))
      ≤ confidenceRadius d R S lam δ X t ω}

end ImprovedLinBandits.OFUL



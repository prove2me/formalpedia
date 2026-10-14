-- Prove2me | Definitions.Def_RobustMultitask_Estimator_Algorithm
-- name    : RobustMultitask_Estimator_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:50.396362+00:00
-- url     : https://prove2.me/theorems/513dce37-ff33-408c-a8e3-fa5c214067a8
-- title:
--   Algorithm 1 and (2), pp. 10–11 — RMEstimator: OLS per task, componentwise trimmed mean β̂†_RM, LASSO centred at β̂†_RM
-- statement:
--   This file defines Algorithm 1 (RMEstimator) of Xu and Bastani on the data $\{(X^j,Y^j)\}_{j\in[N]}$.
--
--   1. **OLS.** For each task, the ordinary least-squares estimator $\widehat\beta^j_{\mathrm{ind}}=(X^{j\top}X^j)^{-1}X^{j\top}Y^j$.
--   2. **Shared estimate (2).** For each coordinate $i\in[d]$, the trimmed mean across tasks
--   $$\widehat\beta^\dagger_{\mathrm{RM},(i)}=\mathrm{TrimmedMean}\big(\{\widehat\beta^j_{\mathrm{ind},(i)}\}_{j\in[N]},\omega\big).$$
--   3. **LASSO step.** For task $j$ and a regularization level $\lambda_j$, the estimate $\widehat\beta^j_{\mathrm{RM}}$ is a global minimizer of
--   $$\beta\ \mapsto\ \frac{1}{n_j}\|X^j\beta-Y^j\|_2^2+\lambda_j\|\beta-\widehat\beta^\dagger_{\mathrm{RM}}\|_1 .$$
--
--   A vector is called an output of the RMEstimator for task $j$ if it is such a minimizer. The file also names the LASSO objective with an arbitrary centre $b$, and the predicate "is a global minimizer" for it, which the proof steps of Proposition 5 use with $b=\widehat\beta^\dagger_{\mathrm{RM}}$.
--
--   **Formalization Note** The arg min is a predicate (`IsLassoMinimizer`, `IsRMEstimate`), never a choice function, so statements quantify over every minimizer. Algorithm 1 initializes $\lambda_j=\lambda/\sqrt{n_j}$; that initialization is not imposed, and $\lambda_j$ is the parameter, as in Proposition 5 ("for any $\lambda_j>0$"). The printed "$X^\top Y^j$" in Algorithm 1 is read as $X^{j\top}Y^j$, as on p. 11. The Lean matrix inverse is $0$ for a singular matrix; every statement using `ols` assumes Assumption 1, under which $X^{j\top}X^j$ is invertible.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, pp. 10–11, Algorithm 1 and §3.2 (Step 1, eq. (2); Step 2)

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_TrimmedMean

namespace RobustMultitask.Estimator

open Matrix

/-- The OLS estimator `β̂_ind = (XᵀX)⁻¹ Xᵀ Y` (Algorithm 1, p. 10; Step 1, p. 11). Lean's matrix
inverse is `0` for a singular matrix; every statement using it assumes Assumption 1, under which
`XᵀX` is invertible. -/
noncomputable def ols {m d : ℕ} (X : Matrix (Fin m) (Fin d) ℝ) (Y : Fin m → ℝ) : Fin d → ℝ :=
  (Xᵀ * X)⁻¹ *ᵥ (Xᵀ *ᵥ Y)

/-- The shared estimate `β̂†_RM` of Step 1, equation (2) (p. 11): componentwise,
`β̂†_RM,(i) = TrimmedMean({β̂ʲ_ind,(i)}_{j∈[N]}, ω)`. -/
noncomputable def sharedEst {N d : ℕ} (n : Fin N → ℕ)
    (X : (j : Fin N) → Matrix (Fin (n j)) (Fin d) ℝ) (ω : ℝ)
    (Y : (j : Fin N) → Fin (n j) → ℝ) : Fin d → ℝ :=
  fun i => trimmedMean (fun j => ols (X j) (Y j) i) ω

/-- The LASSO objective of Step 2, centred at `b`:
`(1/m) ‖Xβ − Y‖₂² + λ ‖β − b‖₁`. -/
noncomputable def lassoObjective {m d : ℕ} (X : Matrix (Fin m) (Fin d) ℝ) (Y : Fin m → ℝ)
    (lam : ℝ) (b β : Fin d → ℝ) : ℝ :=
  (1 / (m : ℝ)) * l2sq (X *ᵥ β - Y) + lam * l1 (β - b)

/-- `βhat` is a global minimizer of the LASSO objective centred at `b`. -/
def IsLassoMinimizer {m d : ℕ} (X : Matrix (Fin m) (Fin d) ℝ) (Y : Fin m → ℝ) (lam : ℝ)
    (b βhat : Fin d → ℝ) : Prop :=
  ∀ β, lassoObjective X Y lam b βhat ≤ lassoObjective X Y lam b β

/-- `βhat` is an output `β̂ʲ_RM` of Algorithm 1 (RMEstimator, p. 10) for task `j`, with trimming
level `ω` and regularization `λ_j = lam`, on the data `{(Xʲ, Yʲ)}`: a global minimizer of
`(1/n_j) ‖Xʲβ − Yʲ‖₂² + λ_j ‖β − β̂†_RM‖₁`, where `β̂†_RM = sharedEst n X ω Y`. The
initialisation `λ_j = λ/√n_j` of Algorithm 1 is not imposed: `λ_j` is the parameter. -/
def IsRMEstimate {N d : ℕ} (n : Fin N → ℕ) (X : (j : Fin N) → Matrix (Fin (n j)) (Fin d) ℝ)
    (Y : (j : Fin N) → Fin (n j) → ℝ) (ω lam : ℝ) (j : Fin N) (βhat : Fin d → ℝ) : Prop :=
  IsLassoMinimizer (X j) (Y j) lam (sharedEst n X ω Y) βhat

end RobustMultitask.Estimator



-- Prove2me | Definitions.Def_WassKF_Reform_expectedLoss
-- name    : WassKF_Reform_expectedLoss
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:09:25.917414+00:00
-- url     : https://prove2.me/theorems/8285ba7b-fe11-444f-bdf8-291a2ec84e72
-- title:
--   (2), p. 3 — the mean square error $\mathbb E^{\mathbb Q}[\|x - \psi(y)\|^2]$ in $[0,\infty]$
-- statement:
--   Let $z = [x; y]$ with $x \in \mathbb R^n$ and $y \in \mathbb R^m$, let $\psi : \mathbb R^m \to \mathbb R^n$ be an estimator of $x$ given $y$, and let $\mathbb Q$ be a measure on $\mathbb R^{n+m}$. The **mean square error** of $\psi$ under $\mathbb Q$ is
--
--   $$
--   \mathbb E^{\mathbb Q}\bigl[\|x - \psi(y)\|^2\bigr] = \int_{\mathbb R^{n+m}} \|x - \psi(y)\|^2 \, \mathbb Q(dz) \in [0, \infty].
--   $$
--
--   It is the objective of the distributionally robust estimation problem (2).
--
--   **Formalization Note** The expectation is the lower Lebesgue integral `∫⁻` of `ENNReal.ofReal` of the published `WassersteinDRO.Shrinkage.estimationLoss ψ z` $= \|x - \psi(y)\|^2$, valued in `ENNReal`. It equals $+\infty$ when the squared error is not integrable, rather than a junk value $0$, so no integrability side condition is needed.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 3, (2)

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_estimationLoss

open MeasureTheory

namespace WassKF.Reform

/-- The mean square error `E^Q[‖x − ψ(y)‖²]` of an estimator `ψ : ℝ^m → ℝ^n` under a distribution
`Q` of `z = [x; y]`, the objective of problem (2) of Shafieezadeh-Abadeh et al.
(arXiv:1809.08830v3, p. 3). It is a lower Lebesgue integral valued in `[0, ∞]`, so it is `+∞`
(not a junk `0`) when the squared error is not integrable. -/
noncomputable def expectedLoss {n m : ℕ}
    (ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (Q : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin m))) : ENNReal :=
  ∫⁻ z, ENNReal.ofReal (WassersteinDRO.Shrinkage.estimationLoss ψ z) ∂Q

end WassKF.Reform



-- Prove2me | Definitions.Def_LRTempElim_PathEstimator
-- name    : LRTempElim_PathEstimator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:24.010082+00:00
-- url     : https://prove2.me/theorems/ae35472a-649f-4c38-bdd1-1cb0850fe173
-- title:
--   Continuous path-moment estimator: $M_t$, $b_t$, readout $m$, influence function $\Psi$ and $C_{\mathrm{path}}(a)$
-- statement:
--   Fix a feature map $\phi:\mathbb R\to\mathbb R^k$ with Jacobian $J_\phi$ and the Gaussian pair law $W=(X_0,X_1)\sim Q_a\otimes P_a$ with linear bridge $X_t=(1-t)X_0+tX_1$. For $t\in[0,1]$ put $\Phi_t(W)=\phi(X_t)$ and $D_t(W)=J_\phi(X_t)(X_1-X_0)$, and define the population quantities
--   $$
--   M_t=\mathbb E[\Phi_t\Phi_t^\top],\qquad b_t=\mathbb E[D_t],\qquad v_t=M_t^{-1}b_t,\qquad m=\int_0^1 v_t\,dt .
--   $$
--   $m$ is the continuous analytic readout (population head). The path influence function is
--   $$
--   \Psi(W)=\int_0^1 M_t^{-1}\big[D_t(W)-\Phi_t(W)\Phi_t(W)^\top v_t\big]\,dt,
--   $$
--   including the inverse-moment term $\Phi_t\Phi_t^\top v_t$. Its covariance is $V_{\mathrm{path}}(a)=\mathrm{Var}_W\,\Psi(W)$, and the covariance-defined function-risk coefficient is
--   $$
--   C_{\mathrm{path}}(a)=\operatorname{tr}\big(\Sigma_{\nu_a}V_{\mathrm{path}}(a)\big),\qquad \Sigma_{\nu_a}=\mathbb E_{\nu_a}[\phi\phi^\top].
--   $$
--   The module also names the bridge mean $\mu_t=a(t-\tfrac12)$ and variance $c_t=(1-t)^2+t^2$.
--
--   These are the objects whose growth in $a$ the goal theorem bounds by $O(1+a^6)$.
--
--   **Formalization Note** $J_\phi$ is the coordinatewise derivative. $b_t$ is the bridge-velocity form $\mathbb E[J_\phi(X_t)(X_1-X_0)]$ used in (41) and (51). $M_t^{-1}$ is the matrix inverse (which Lean sets to $0$ on a singular matrix; $M_t$ is invertible for the Gaussian family). Time integrals are interval integrals over $[0,1]$. $\mathrm{Var}_W\Psi(W)$ is the covariance matrix $\mathbb E[(\Psi-\mathbb E\Psi)(\Psi-\mathbb E\Psi)^\top]$ of the law of $\Psi(W)$, computed with the published definition `WassersteinDRO.Guarantees.covarianceMatrix`.
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), eq. (41), p.17 (pdf p.19); eq. (51) and §A.2.3, p.20 (pdf p.22); proof of Proposition A.2, p.15 (pdf p.17); C(a) = tr(Σ_{ν_a}V_a), p.7 (pdf p.9)

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_covarianceMatrix
import Definitions.Def_LRTempElim_Setting

open MeasureTheory ProbabilityTheory Matrix

namespace LRTempElim

/-!
# The continuous path-moment estimator: population moments, readout, influence function

W. Chen, Y. Wu, J. Yang, D. Zeng, *Likelihood-Ratio Learning under Weak Overlap via Analytic
Temporal Elimination*, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee65139…),
eq. (41) (p.17, pdf p.19), eq. (51) and §A.2.3 (p.20, pdf p.22), Proposition A.2 (p.15, pdf p.17),
eq. (45) and the coefficient `C(a) = tr(Σ_{ν_a}V_a)` (p.7, pdf p.9).

"For the continuous path estimator, put `Φ_t(W) = ϕ(X_t)`, `D_t(W) = J_ϕ(X_t)(X₁ − X₀)` and
`v_t = M_t⁻¹b_t`. Differentiation of `M⁻¹b` gives the influence function
`Ψ(W) = ∫₀¹ M_t⁻¹[D_t(W) − Φ_tΦ_t⊤v_t] dt.` (51) … Thus `V_prof = Var_W Ψ(W)`" (p.20), with
`M_t = E[Φ_tΦ_t⊤]`, `b_t = E[D_t]`, `m = ∫₀¹ v_t dt` (eq. (41), p.17).

**Formalization Note.**
* Generic in the feature map `ϕ : ℝ → ℝᵏ` (Proposition A.2 uses `k = 2` and `k = 3`); the
  Jacobian `J_ϕ` is the coordinatewise derivative `deriv (fun x => ϕ x i)`.
* `b_t = E[J_ϕ(X_t)(X₁ − X₀)]` (eqs. (41), (51)) — the bridge-velocity form, used everywhere.
* `M_t⁻¹` is `Matrix.inv`, whose value on a singular matrix is `0`; theorems using these
  objects assert or assume invertibility where it matters.
* Time integrals are interval integrals `∫ t in (0:ℝ)..1`.
* `Vpath ϕ a = Var_W Ψ(W)` is the covariance matrix `E[(Ψ − EΨ)(Ψ − EΨ)⊤]` of the law of `Ψ(W)`
  under `W ∼ Q_a ⊗ P_a` (the published `WassersteinDRO.Guarantees.covarianceMatrix`); the law is
  the pushforward of `pairLaw a` under `Ψ`, viewed in `EuclideanSpace ℝ (Fin k)`.
* `Cpath ϕ a = tr(Σ_{ν_a} V_path(a))` (p.7). With `E Ψ = 0` this equals `E‖Σ^{1/2}Ψ(W)‖²` of
  eq. (45); the covariance form is the paper's definition in Theorem 2 ("covariance-defined").
* `bridgeMean a t = µ_t = a(t − 1/2)` and `bridgeVar t = c_t = (1 − t)² + t²` are the mean and
  variance of the bridge marginal (proof of Proposition A.2, p.15; §A.2.3, p.20); `c′_t` is
  written `deriv bridgeVar t`.
-/

/-- The population moment matrix `M_t = E[ϕ(X_t)ϕ(X_t)⊤]` on the linear bridge (eq. (41)). -/
noncomputable def momentMat {k : ℕ} (ϕ : ℝ → Fin k → ℝ) (a t : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ∫ W, ϕ (bridge t W) i * ϕ (bridge t W) j ∂(pairLaw a)

/-- The pathwise feature derivative `D_t(W) = J_ϕ(X_t)(X₁ − X₀)` (eq. (51)). -/
noncomputable def pathDeriv {k : ℕ} (ϕ : ℝ → Fin k → ℝ) (t : ℝ) (W : ℝ × ℝ) : Fin k → ℝ :=
  fun i => deriv (fun x => ϕ x i) (bridge t W) * (W.2 - W.1)

/-- The drift vector `b_t = E[D_t(W)] = E[J_ϕ(X_t)(X₁ − X₀)]` (eqs. (41), (51)). -/
noncomputable def driftVec {k : ℕ} (ϕ : ℝ → Fin k → ℝ) (a t : ℝ) : Fin k → ℝ :=
  fun i => ∫ W, pathDeriv ϕ t W i ∂(pairLaw a)

/-- The timewise coefficient `v_t = M_t⁻¹b_t` (eq. (41)). -/
noncomputable def vCoef {k : ℕ} (ϕ : ℝ → Fin k → ℝ) (a t : ℝ) : Fin k → ℝ :=
  (momentMat ϕ a t)⁻¹ *ᵥ driftVec ϕ a t

/-- The continuous analytic readout (population head) `m = ∫₀¹ v_t dt` (eq. (41)). -/
noncomputable def readout {k : ℕ} (ϕ : ℝ → Fin k → ℝ) (a : ℝ) : Fin k → ℝ :=
  fun i => ∫ t in (0 : ℝ)..1, vCoef ϕ a t i

/-- The bracket of eq. (51), `D_t(W) − Φ_t(W)Φ_t(W)⊤v_t` with `Φ_t(W) = ϕ(X_t)`. -/
noncomputable def pathBracket {k : ℕ} (ϕ : ℝ → Fin k → ℝ) (a t : ℝ) (W : ℝ × ℝ) : Fin k → ℝ :=
  pathDeriv ϕ t W - (ϕ (bridge t W) ⬝ᵥ vCoef ϕ a t) • ϕ (bridge t W)

/-- The path influence function `Ψ(W) = ∫₀¹ M_t⁻¹[D_t(W) − Φ_tΦ_t⊤v_t] dt` (eq. (51)),
including the inverse-moment term. -/
noncomputable def influence {k : ℕ} (ϕ : ℝ → Fin k → ℝ) (a : ℝ) (W : ℝ × ℝ) : Fin k → ℝ :=
  fun i => ∫ t in (0 : ℝ)..1, ((momentMat ϕ a t)⁻¹ *ᵥ pathBracket ϕ a t W) i

/-- `V_path(a) = Var_W Ψ(W)`, the covariance matrix of `Ψ(W)` under `W ∼ Q_a ⊗ P_a`
(§A.2.3, p.20). -/
noncomputable def Vpath {k : ℕ} (ϕ : ℝ → Fin k → ℝ) (a : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  WassersteinDRO.Guarantees.covarianceMatrix
    ((pairLaw a).map fun W => WithLp.toLp 2 (influence ϕ a W))

/-- The covariance-defined function-risk coefficient `C_path(a) = tr(Σ_{ν_a} V_path(a))`
(p.7). -/
noncomputable def Cpath {k : ℕ} (ϕ : ℝ → Fin k → ℝ) (a : ℝ) : ℝ :=
  Matrix.trace (secondMoment ϕ (nu a) * Vpath ϕ a)

/-- The bridge mean `µ_t = a(t − 1/2)` (proof of Proposition A.2, p.15). -/
noncomputable def bridgeMean (a t : ℝ) : ℝ := a * (t - 1 / 2)

/-- The bridge variance `c_t = (1 − t)² + t²` (proof of Proposition A.2, p.15). -/
def bridgeVar (t : ℝ) : ℝ := (1 - t) ^ 2 + t ^ 2

end LRTempElim



-- Prove2me | Definitions.Def_HigherOrderId_Certify_Fisher
-- name    : HigherOrderId_Certify_Fisher
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:17:42.972828+00:00
-- url     : https://prove2.me/theorems/4e6ae818-8659-45d6-8f92-4078629fc1c7
-- title:
--   Fisher information of the gradient and full value–gradient releases, and the efficient covariance Σ^eff
-- statement:
--   For a design $(x_e,n_e)_{e\le E}$ and noise level $\sigma$, the release (52) is a Gaussian experiment with known diagonal covariance whose mean depends linearly on $(b,Q)$ (up to the known intercept $\tfrac12$). Its Fisher information operators are therefore given by their quadratic forms at a perturbation $(h,H)\in\mathbb R^d\times S^d_0$:
--   $$\langle (h,H),I_{\mathrm{grad}}(h,H)\rangle=\sum_e\frac{n_e}{\sigma^2}\|h+Hx_e\|_2^2,\qquad \langle (h,H),I_{\mathrm{full}}(h,H)\rangle=\langle (h,H),I_{\mathrm{grad}}(h,H)\rangle+\sum_e\frac{n_e}{\sigma^2}\Big(h^\top x_e+\tfrac12x_e^\top Hx_e\Big)^2 .$$
--   In the coordinates $\vartheta=(b_1,\dots,b_d,\{Q_{ij}\}_{i<j})$ of (99) (a unit change of $Q_{ij}$ changes both entries $(i,j)$ and $(j,i)$), $I_{\mathrm{full}}$ is a square matrix indexed by these coordinates. The covariance of the generalized least-squares sufficient statistic for $\vartheta$ in the complete value–gradient channel is $\Sigma^{\mathrm{eff}}=I_{\mathrm{full}}^{-1}$, used in the full-rank case $I_{\mathrm{full}}\succ0$.
--
--   **Formalization Note.** `gradFisher`, `fullFisher` are the quadratic forms; `fullFisherMat` is the matrix in coordinates (99); `SigmaEff` is its matrix inverse `⁻¹` (Mathlib returns 0 for a singular matrix, so it is only used under `PosDef`).
-- source:
--   Zhang, Yan, Qiao, Yu, The Higher-Order Identifiability Paradox: Learning and Certifying Hypergraph Order, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 21, Lemma B.1 and Eq. (57); p. 30, Eqs. (99), (101)

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Release

open Matrix

namespace HigherOrderId.Certify

/-!
# Fisher information of the gradient and value–gradient releases, and the efficient covariance

Zhang, Yan, Qiao, Yu, *The Higher-Order Identifiability Paradox: Learning and Certifying
Hypergraph Order*, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 21, Lemma B.1 and
Eq. (57); p. 30, Eqs. (99), (101).

The release (52) is a Gaussian experiment with known diagonal covariance and mean linear in
`(b, Q)` (up to the known intercept `1/2`). Its Fisher information is therefore the quadratic form
`Σ_e (n_e/σ²) ‖∂(mean_e)(h, H)‖²` in a perturbation `(h, H) ∈ ℝ^d × S^d_0`, where the
derivative of the gradient mean is `h + Hx_e` and that of the value mean is
`hᵀx_e + x_eᵀHx_e/2`.

* `gradFisher D σ h H` is the quadratic form of `I_grad` (gradient releases only).
* `fullFisher D σ h H` is the quadratic form of `I_full` (joint value–gradient releases).
* `fullFisherMat D σ` is the matrix of `I_full` in the coordinates `ϑ` of (99):
  `b_1, …, b_d` and `Q_ij` for `i < j` (a unit change of `Q_ij` moves both entries
  `(i, j)` and `(j, i)`).
* `SigmaEff D σ` is the covariance of the generalized least-squares sufficient statistic for
  `ϑ`, the inverse Fisher matrix `I_full⁻¹` (meaningful when `I_full` is positive definite,
  the full-rank case).
-/

/-- Quadratic form of the Fisher information `I_grad` of the gradient releases at `(h, H)`. -/
noncomputable def gradFisher {d E : ℕ} (D : Design d E) (σ : ℝ) (h : Fin d → ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ e, ((D.n e : ℝ) / σ ^ 2) * ∑ i, (h i + (H *ᵥ D.x e) i) ^ 2

/-- Quadratic form of the Fisher information carried by the value releases at `(h, H)`. -/
noncomputable def valueFisher {d E : ℕ} (D : Design d E) (σ : ℝ) (h : Fin d → ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ e, ((D.n e : ℝ) / σ ^ 2) * (h ⬝ᵥ D.x e + (1 / 2) * (D.x e ⬝ᵥ (H *ᵥ D.x e))) ^ 2

/-- Quadratic form of the Fisher information `I_full` of the joint value–gradient releases. -/
noncomputable def fullFisher {d E : ℕ} (D : Design d E) (σ : ℝ) (h : Fin d → ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  gradFisher D σ h H + valueFisher D σ h H

/-- The `b`-part of the unit perturbation of the `ϑ`-coordinate `s`. -/
noncomputable def thetaB {d : ℕ} : ThetaIdx d → Fin d → ℝ
  | .inl i => Pi.single i 1
  | .inr _ => 0

/-- The `Q`-part of the unit perturbation of the `ϑ`-coordinate `s`: `E_ij + E_ji` for
`s = Q_ij`. -/
def thetaQ {d : ℕ} : ThetaIdx d → Matrix (Fin d) (Fin d) ℝ
  | .inl _ => 0
  | .inr p => Matrix.single p.1.1 p.1.2 1 + Matrix.single p.1.2 p.1.1 1

/-- The Fisher information matrix of the full value–gradient release in the coordinates (99). -/
noncomputable def fullFisherMat {d E : ℕ} (D : Design d E) (σ : ℝ) :
    Matrix (ThetaIdx d) (ThetaIdx d) ℝ :=
  fun s s' => ∑ e, ((D.n e : ℝ) / σ ^ 2) *
    ((thetaB s ⬝ᵥ D.x e + (1 / 2) * (D.x e ⬝ᵥ (thetaQ s *ᵥ D.x e))) *
        (thetaB s' ⬝ᵥ D.x e + (1 / 2) * (D.x e ⬝ᵥ (thetaQ s' *ᵥ D.x e))) +
      ∑ i, (thetaB s i + (thetaQ s *ᵥ D.x e) i) * (thetaB s' i + (thetaQ s' *ᵥ D.x e) i))

/-- `Σ^eff`: the covariance of the generalized least-squares sufficient statistic for `ϑ` in the
complete value–gradient channel, `I_full⁻¹` in the coordinates (99). -/
noncomputable def SigmaEff {d E : ℕ} (D : Design d E) (σ : ℝ) :
    Matrix (ThetaIdx d) (ThetaIdx d) ℝ :=
  (fullFisherMat D σ)⁻¹

end HigherOrderId.Certify



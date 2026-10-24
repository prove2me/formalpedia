-- Prove2me | Definitions.Def_SynDigits_Ridge_Model
-- name    : SynDigits_Ridge_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:14.067655+00:00
-- url     : https://prove2.me/theorems/dc23fa2f-c534-439b-940e-e89fbf76fc97
-- title:
--   §3.2, §4.1–4.2, pp. 6, 9, 11 — sample moments, Ridge fit-and-transfer estimator, population Ridge target and residual
-- statement:
--   This file fixes the objects of the Ridge instantiation of the fit-and-transfer method of SYN-DIGITS.
--
--   There are $n$ users and $m$ existing questions. The human responses form $Y \in \mathbb{R}^{n\times m}$, the digital-twin responses to the same questions form $\tilde Y \in \mathbb{R}^{n\times m}$, and the twin responses to the new question form $\tilde Y_v \in \mathbb{R}^n$.
--
--   1. The Euclidean norm of $x \in \mathbb{R}^k$ is $\|x\|_2 = \sqrt{x^\top x}$.
--   2. The sample second moment and cross moment of the twin system are
--   $$\hat{\tilde\Sigma} = \frac1n \tilde Y^\top \tilde Y \in \mathbb{R}^{m\times m}, \qquad \hat{\tilde\gamma} = \frac1n \tilde Y^\top \tilde Y_v \in \mathbb{R}^m .$$
--   3. For $S \in \mathbb{R}^{m\times m}$, $g \in \mathbb{R}^m$ and $\lambda \in \mathbb{R}$, the Ridge coefficients are $(S + \lambda I)^{-1} g$.
--   4. The Ridge fit on the twin system is $\hat\beta = (\hat{\tilde\Sigma} + \lambda I)^{-1}\hat{\tilde\gamma}$, the unique solution of the normal equation $(\hat{\tilde\Sigma}+\lambda I)\beta = \hat{\tilde\gamma}$, i.e. the minimizer of $\frac1n\|\tilde Y_v - \tilde Y\beta\|_2^2 + \lambda\|\beta\|_2^2$ when $\hat{\tilde\Sigma}+\lambda I$ is invertible.
--   5. The fit-and-transfer prediction applies the twin-fitted coefficients to the **human** responses: $\hat Y_v = Y\hat\beta$.
--   6. For a population second moment $\tilde\Sigma$ and cross moment $\tilde\gamma$, the population Ridge target is $\beta^* = (\tilde\Sigma + \lambda I)^{-1}\tilde\gamma$ and the structural residual is $r = Y_v - Y\beta^*$, where $Y_v \in \mathbb{R}^n$ are the human responses to the new question.
--
--   These are the quantities of Theorem 4.1 (p. 11) and its proof (Appendix B.1). The latent factor model $Y = UV^\top + \mathcal E$ of §4.1 enters the theorems as hypotheses, not as a definition.
--
--   **Formalization Note** Vectors are `Fin k → ℝ` and matrices `Matrix (Fin a) (Fin b) ℝ`. Lean's matrix inverse is total and returns $0$ on a singular matrix, and $1/n = 0$ at $n = 0$; the theorems add the hypotheses under which every inverse used is a genuine inverse. The spectral norm and $\sigma_{\min}$ come from the referenced definition `GaussianMatrix_basic`.
-- source:
--   Fan, Huang, Peng, Wang, Wu, SYN-DIGITS: A Synthetic Control Framework for Calibrated Digital Twin Simulation, arXiv:2604.07513v1, p. 6, §3.2 and Algorithm 1, Table 1 (Ridge); p. 9, (4.1)–(4.2); p. 11, Theorem 4.1 preamble; p. 32, Appendix B.1

import Mathlib
import Definitions.Def_GaussianMatrix_basic

namespace SynDigits.Ridge

open Matrix

/-- Euclidean norm `‖x‖₂ = √(x ⬝ x)` of a vector `x ∈ ℝᵏ`, in the convention of
`GaussianMatrix.sMin`. -/
noncomputable def vnorm {k : ℕ} (x : Fin k → ℝ) : ℝ := Real.sqrt (x ⬝ᵥ x)

/-- Sample second-moment matrix of the twin responses to the `m` existing questions,
`Σ̂̃ = (1/n) Ỹᵀ Ỹ`. -/
noncomputable def sampleCov {n m : ℕ} (Yt : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  (1 / (n : ℝ)) • (Ytᵀ * Yt)

/-- Sample cross-moment vector between the twin responses to the existing questions and to
the new question, `γ̂̃ = (1/n) Ỹᵀ Ỹ_v`. -/
noncomputable def sampleCross {n m : ℕ} (Yt : Matrix (Fin n) (Fin m) ℝ) (ytv : Fin n → ℝ) :
    Fin m → ℝ :=
  (1 / (n : ℝ)) • (Ytᵀ *ᵥ ytv)

/-- Ridge coefficients from a second-moment matrix `S` and a cross-moment vector `g`:
`(S + λI)⁻¹ g`. (Lean's matrix inverse is total and returns `0` on a singular matrix.) -/
noncomputable def ridgeCoef {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (g : Fin m → ℝ) (lam : ℝ) :
    Fin m → ℝ :=
  (S + lam • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ *ᵥ g

/-- The Ridge fit on the digital-twin system, `β̂ = (Σ̂̃ + λI)⁻¹ γ̂̃`: when `Σ̂̃ + λI` is
invertible it is the unique solution of the normal equation `(Σ̂̃ + λI) β = γ̂̃`, i.e. the minimizer
of `(1/n)‖Ỹ_v − Ỹ β‖₂² + λ‖β‖₂²`. -/
noncomputable def ridgeFit {n m : ℕ} (Yt : Matrix (Fin n) (Fin m) ℝ) (ytv : Fin n → ℝ)
    (lam : ℝ) : Fin m → ℝ :=
  ridgeCoef (sampleCov Yt) (sampleCross Yt ytv) lam

/-- Fit-and-transfer prediction of the human responses to the new question:
the twin-fitted coefficients applied to the human response matrix, `Ŷ_v = Y β̂`. -/
noncomputable def ridgePredict {n m : ℕ} (Y Yt : Matrix (Fin n) (Fin m) ℝ) (ytv : Fin n → ℝ)
    (lam : ℝ) : Fin n → ℝ :=
  Y *ᵥ ridgeFit Yt ytv lam

/-- Population Ridge target `β* = (Σ̃ + λI)⁻¹ γ̃`. -/
noncomputable def betaStar {m : ℕ} (Sig : Matrix (Fin m) (Fin m) ℝ) (gam : Fin m → ℝ)
    (lam : ℝ) : Fin m → ℝ :=
  ridgeCoef Sig gam lam

/-- Structural residual `r = Y_v − Y β*`. -/
noncomputable def resid {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℝ) (Yv : Fin n → ℝ)
    (Sig : Matrix (Fin m) (Fin m) ℝ) (gam : Fin m → ℝ) (lam : ℝ) : Fin n → ℝ :=
  Yv - Y *ᵥ betaStar Sig gam lam

end SynDigits.Ridge



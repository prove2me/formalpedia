-- Prove2me | Definitions.Def_PolyakJuditsky_Averaging_Model
-- name    : PolyakJuditsky_Averaging_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:37:12.921269+00:00
-- url     : https://prove2.me/theorems/33284504-1b80-44dc-bc4c-ae3d8e739339
-- title:
--   Averaged stochastic approximation (Eq. (7)) and the matrices $X_j^t$, $\bar X_j^t$, $\varphi_j^t$, $\alpha_j^t$, $w_j^t$ of the Appendix
-- statement:
--   This file fixes the objects of Polyak and Juditsky's analysis of averaged stochastic approximation. Points live in $\mathbb R^N$ with the Euclidean norm $|\cdot|$; matrices are real $N\times N$ matrices acting on $\mathbb R^N$ in the usual way.
--
--   1. **The recursion of Eq. (7).** Given a starting point $x_0\in\mathbb R^N$, step sizes $(\gamma_t)_{t\ge 1}$, a map $R:\mathbb R^N\to\mathbb R^N$ and disturbances $(\xi_t)_{t\ge1}$, set
--   $$
--   x_t = x_{t-1}-\gamma_t\bigl(R(x_{t-1})+\xi_t\bigr),\quad t\ge 1,\qquad \bar x_t=\frac1t\sum_{i=0}^{t-1}x_i .
--   $$
--   The average $\bar x_t$ includes $x_0$ and excludes $x_t$. When the disturbances are random, $\xi_t=\xi_t(\omega)$, the iterate $x_t(\omega)$ and its average $\bar x_t(\omega)$ are obtained by running the same recursion along each sample path; the starting point $x_0$ is nonrandom. With $R(x)=Ax-b$ this is the linear algorithm (2), and with $R(x)=Ax$, $x_0=\Delta_0$ it is the error recursion (A8).
--   2. **Spectral condition.** A matrix $A$ satisfies $\operatorname{Re}\lambda_i(A)>0$ for all $i$ when every complex eigenvalue of $A$ has positive real part (equivalently $-A$ is Hurwitz).
--   3. **Condition (4) of Assumption 2.2.** The steps satisfy $\gamma_t>0$ for $t\ge1$, $\gamma_t\to0$, and $(\gamma_t-\gamma_{t+1})/\gamma_t=o(\gamma_t)$.
--   4. **The matrices of (A1).** $X_j^j=I$ and $X_j^{t+1}=X_j^t-\gamma_tAX_j^t$ for $t\ge j$, so $X_j^t=(I-\gamma_{t-1}A)\cdots(I-\gamma_jA)$; $\bar X_j^t=\gamma_j\sum_{i=j}^{t-1}X_j^i$ and $\varphi_j^t=A^{-1}-\bar X_j^t$.
--   5. **The matrices of the proof of Lemma 2.** $\alpha_j^t=\gamma_j\sum_{i=j}^{t-1}\prod_{k=j+1}^{i}(I-\gamma_kA)=\gamma_j\sum_{i=j}^{t-1}X_{j+1}^{i+1}$, $\alpha_t=\alpha_0^t$, and $w_j^t=\alpha_j^t-A^{-1}$.
--   6. **Matrix norm.** $\|M\|$ is the operator norm of $M$ on Euclidean $\mathbb R^N$.
--
--   These objects are shared by every statement of the mission: the goal and its proof steps are about the iterates of Eq. (7), and the matrix lemmas of the Appendix are about $X_j^t$, $\varphi_j^t$, $\alpha_j^t$ and $w_j^t$.
--
--   **Formalization Note** The step size $\gamma_0$ and the noise $\xi_0$ are never used by the recursion; the Appendix's matrices do use $\gamma_0$. $X_j^t$ is set to $I$ for $t<j$ and $\bar x_0=0$; neither value is used by any statement. The paper writes $X_j^t=\prod_{i=j}^{t}(I-\gamma_iA)$ on p. 847, which disagrees with (A1) by one index; (A1) is followed. The paper does not name the matrix norm; every statement using it is of the form "$\le K$ for some $K$" or "$\to0$", which does not depend on the choice.
-- source:
--   Polyak, Juditsky, Acceleration of stochastic approximation by averaging, SIAM J. Control Optim. 30 (1992), p. 840, Eq. (7); p. 839, Assumptions 2.1–2.2, Eq. (4); p. 844, Eq. (A1); p. 847, proof of Lemma 2

import Mathlib

open MeasureTheory Filter Topology

namespace PolyakJuditsky.Averaging

/-- The deterministic recursion of Eq. (7) driven by a fixed noise sequence `ξ`:
`x 0 = x₀` and `x t = x (t-1) - γ t • (R (x (t-1)) + ξ t)` for `t ≥ 1`.
The step sizes `γ t` and the noise `ξ t` are used for `t ≥ 1` only. -/
noncomputable def detIterate {N : ℕ} (x₀ : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ : ℕ → EuclideanSpace ℝ (Fin N)) : ℕ → EuclideanSpace ℝ (Fin N)
  | 0 => x₀
  | t + 1 => detIterate x₀ γ R ξ t - γ (t + 1) • (R (detIterate x₀ γ R ξ t) + ξ (t + 1))

/-- The averaged iterate `x̄_t = (1/t) ∑_{i=0}^{t-1} x_i` of Eq. (7) (equal to `0` at `t = 0`). -/
noncomputable def detAverage {N : ℕ} (x₀ : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ : ℕ → EuclideanSpace ℝ (Fin N)) (t : ℕ) : EuclideanSpace ℝ (Fin N) :=
  (t : ℝ)⁻¹ • ∑ i ∈ Finset.range t, detIterate x₀ γ R ξ i

/-- The stochastic approximation process of Eq. (7): `x_t(ω)` is the recursion `detIterate`
run along the noise path `t ↦ ξ t ω`, from the nonrandom starting point `x₀`. -/
noncomputable def saIterate {N : ℕ} {Ω : Type*} (x₀ : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (t : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin N) :=
  detIterate x₀ γ R (fun s => ξ s ω) t

/-- The averaged stochastic approximation estimate `x̄_t(ω) = (1/t) ∑_{i=0}^{t-1} x_i(ω)` of
Eq. (7). -/
noncomputable def saAverage {N : ℕ} {Ω : Type*} (x₀ : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (t : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin N) :=
  detAverage x₀ γ R (fun s => ξ s ω) t

/-- The matrix `M` acting on `ℝ^N` (Euclidean space) as a linear map, `v ↦ M v`. -/
noncomputable def matApply {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (v : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  Matrix.toEuclideanLin M v

/-- The operator norm of `M` on Euclidean `ℝ^N` (the matrix norm `‖M‖` of the Appendix). -/
noncomputable def matNorm {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

/-- `Re λ_i(A) > 0` for every (complex) eigenvalue of `A`, i.e. `-A` is Hurwitz
(Assumption 2.1; the eigenvalue part of Assumption 3.2). -/
def EigenRePos {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ μ ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), 0 < μ.re

/-- Condition (4) of Assumption 2.2 for steps indexed from `t = 1`:
`γ_t > 0` for `t ≥ 1`, `γ_t → 0`, and `(γ_t - γ_{t+1}) / γ_t = o(γ_t)`. -/
def StepCondition4 (γ : ℕ → ℝ) : Prop :=
  (∀ t, 1 ≤ t → 0 < γ t) ∧ Tendsto γ atTop (𝓝 0) ∧
    (fun t => (γ t - γ (t + 1)) / γ t) =o[atTop] γ

/-- The matrices `X_j^t` of (A1): `X_j^j = I` and `X_j^{t+1} = X_j^t - γ_t A X_j^t` for `t ≥ j`,
so `X_j^t = (I - γ_{t-1} A) ⋯ (I - γ_j A)` for `t ≥ j`. For `t < j` the value is `I`
(never used). -/
noncomputable def lemX {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j : ℕ) :
    ℕ → Matrix (Fin N) (Fin N) ℝ
  | 0 => 1
  | t + 1 => if j ≤ t then lemX A γ j t - γ t • (A * lemX A γ j t) else 1

/-- `X̄_j^t = γ_j ∑_{i=j}^{t-1} X_j^i` of (A1). -/
noncomputable def lemXbar {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j t : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  γ j • ∑ i ∈ Finset.Ico j t, lemX A γ j i

/-- `φ_j^t = A⁻¹ - X̄_j^t` (Appendix, before Lemma 1). -/
noncomputable def lemPhi {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j t : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  A⁻¹ - lemXbar A γ j t

/-- `α_j^t = γ_j ∑_{i=j}^{t-1} ∏_{k=j+1}^{i} (I - γ_k A) = γ_j ∑_{i=j}^{t-1} X_{j+1}^{i+1}`
(proof of Lemma 2, p. 847). -/
noncomputable def lemAlpha {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j t : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  γ j • ∑ i ∈ Finset.Ico j t, lemX A γ (j + 1) (i + 1)

/-- `w_j^t = α_j^t - A⁻¹` (proof of Lemma 2, p. 847). -/
noncomputable def lemW {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (γ : ℕ → ℝ) (j t : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  lemAlpha A γ j t - A⁻¹

end PolyakJuditsky.Averaging



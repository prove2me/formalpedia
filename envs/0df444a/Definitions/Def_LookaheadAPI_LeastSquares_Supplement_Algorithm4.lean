-- Prove2me | Definitions.Def_LookaheadAPI_LeastSquares_Supplement_Algorithm4
-- name    : LookaheadAPI_LeastSquares_Supplement_Algorithm4
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:51:57.118801+00:00
-- url     : https://prove2.me/theorems/b08180e8-a340-405a-bccb-93424ee385c5
-- title:
--   Algorithm 4 (gradient descent): $\eta$ gradient steps with step size $\gamma$ on the least-squares objective, after an $H$-step lookahead
-- statement:
--   This module defines Algorithm 4 of Winnicki, Lubars, Livesay and Srikant, the **gradient descent algorithm**, a variant of least-squares approximate policy iteration with lookahead (Algorithm 2) in which the least-squares fit is replaced by a fixed number of gradient steps.
--
--   The model is the finite discounted MDP $(\mathcal S,\mathcal A,P,r,\alpha)$ of the published definition `LookaheadAPI.LeastSquares.MDP`, with policy operators $T_\mu$, Bellman operator $T$ and values $J^\mu$. A feature matrix $\Phi\in\mathbb R^{|\mathcal S|\times d}$ has the feature vector $\phi(i)\in\mathbb R^d$ of state $i$ as its row $i$. For a set of states $\mathcal D\subseteq\mathcal S$, $\Phi_{\mathcal D}$ is the submatrix of the rows $i\in\mathcal D$ and $\mathcal P_{\mathcal D}$ is the $0/1$ matrix that extracts the entries indexed by $\mathcal D$.
--
--   1. **Gradient step.** For a target vector $\hat J$ and step size $\gamma\in\mathbb R$, the least-squares objective is $c(\theta;\hat J)=\tfrac12\sum_{i\in\mathcal D}\big((\Phi\theta)(i)-\hat J(i)\big)^2$, with gradient $\nabla_\theta c(\theta;\hat J)=\Phi_{\mathcal D}^\top(\Phi_{\mathcal D}\theta-\mathcal P_{\mathcal D}\hat J)$. One step (11) maps
--   $$\theta\ \longmapsto\ \theta-\gamma\,\Phi_{\mathcal D}^\top\big(\Phi_{\mathcal D}\theta-\mathcal P_{\mathcal D}\hat J\big).$$
--
--   2. **A run of Algorithm 4** with evaluation sets $\mathcal D_k$, rollout length $m$, lookahead depth $H$, lookahead accuracy $\varepsilon_{LA}$, step size $\gamma$ and number of gradient steps $\eta$ is a sequence of parameters $\theta_k$, estimates $J_k$, policies $\mu_k$ and noise vectors $w_k$ such that $J_0=\Phi\theta_0$ and, for every $k\ge0$:
--      - $\|T^HJ_k-T_{\mu_{k+1}}T^{H-1}J_k\|_\infty\le\varepsilon_{LA}$ (Step 2);
--      - with $\hat J^{\mu_{k+1}}=T^m_{\mu_{k+1}}T^{H-1}J_k+w_{k+1}$ (Step 3), $\theta_{k+1,0}=\theta_k$ and $\theta_{k+1,\ell}=\theta_{k+1,\ell-1}-\gamma\nabla_\theta c(\theta;\hat J^{\mu_{k+1}})|_{\theta_{k+1,\ell-1}}$ for $\ell=1,\dots,\eta$, computed on $\mathcal D_k$ (Step 4);
--      - $\theta_{k+1}=\theta_{k+1,\eta}$ and $J_{k+1}=\Phi\theta_{k+1}$ (Step 5).
--
--   The error bounds of Appendix E and Theorem 2 are stated for every run of this algorithm.
--
--   **Formalization Note** The gradient is written out rather than taken from Mathlib's `gradient`. The inner loop is the $\eta$-fold iterate of the gradient step. The noise $w_{k+1}$ is a vector on all of $\mathcal S$; only its entries on $\mathcal D_k$ enter the algorithm. The initial policy $\mu_0$ and $w_0$ are not produced by the algorithm and are left free, as in the published run predicate of Algorithm 2. The objects `IsLookahead` and `noisyReturn` are reused from the published `LookaheadAPI.LeastSquares.Algorithms`.
-- source:
--   arXiv:2109.13419v7, p. 16, Algorithm 4 (Gradient Descent Algorithm), eq. (11)

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
import Definitions.Def_LookaheadAPI_LeastSquares_Algorithms

namespace LookaheadAPI.LeastSquares.Supplement

open Matrix

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]

/-- One gradient step (11) of Step 4 of Algorithm 4 (arXiv:2109.13419v7, p. 16) with step size
`γ` on the least-squares objective `c(θ; Ĵ) = ½ ∑_{i ∈ 𝒟} ((Φθ)(i) − Ĵ(i))²` of the evaluation set
`𝒟`: `θ ↦ θ − γ ∇_θ c(θ; Ĵ)`, where `∇_θ c(θ; Ĵ) = Φ_𝒟^⊤ (Φ_𝒟 θ − 𝒫_𝒟 Ĵ)` (written out). -/
def gdStep {d : ℕ} (Φ : Matrix S (Fin d) ℝ) (D : Finset S) (γ : ℝ) (Jhat : S → ℝ)
    (θ : Fin d → ℝ) : Fin d → ℝ :=
  θ - γ • ((featuresOn Φ D)ᵀ *ᵥ (featuresOn Φ D *ᵥ θ - restrictTo D *ᵥ Jhat))

/-- A run of Algorithm 4, "Gradient Descent Algorithm" (p. 16), with inputs `θ_0 = θ 0`, `m`,
`H`, features `Φ`, evaluation sets `𝒟_k = D k`, step size `γ` and number of gradient steps `η`:
Step 1 (`J_0 = Φ θ_0`), and for every `k ≥ 0`:
Step 2 (`μ_{k+1}` is an `ε_LA`-lookahead policy for `J_k`),
Steps 3–4 (`θ_{k+1,0} = θ_k`, `θ_{k+1,ℓ} = θ_{k+1,ℓ−1} − γ ∇_θ c(θ; Ĵ^{μ_{k+1}})|_{θ_{k+1,ℓ−1}}`
for `ℓ = 1, …, η`, with `Ĵ^{μ_{k+1}} = T^m_{μ_{k+1}} T^{H−1} J_k + w_{k+1}` on `𝒟_k`), and
Step 5 (`θ_{k+1} = θ_{k+1,η}`, `J_{k+1} = Φ θ_{k+1}`).
The policy `μ 0` and the noise `w 0` are not produced by the algorithm and are left free. -/
def IsRunAlg4 {d : ℕ} (M : MDP S A) (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S) (m H : ℕ)
    (εLA γ : ℝ) (η : ℕ) (J : ℕ → S → ℝ) (μ : ℕ → S → A) (w : ℕ → S → ℝ)
    (θ : ℕ → Fin d → ℝ) : Prop :=
  J 0 = Φ *ᵥ θ 0 ∧
  ∀ k : ℕ,
    IsLookahead M H εLA (J k) (μ (k + 1)) ∧
    θ (k + 1) =
      (gdStep Φ (D k) γ (noisyReturn M m H (J k) (μ (k + 1)) (w (k + 1))))^[η] (θ k) ∧
    J (k + 1) = Φ *ᵥ θ (k + 1)

end LookaheadAPI.LeastSquares.Supplement



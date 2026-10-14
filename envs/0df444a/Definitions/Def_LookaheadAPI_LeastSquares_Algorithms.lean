-- Prove2me | Definitions.Def_LookaheadAPI_LeastSquares_Algorithms
-- name    : LookaheadAPI_LeastSquares_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:53:02.065+00:00
-- url     : https://prove2.me/theorems/3a7685e8-2584-4f6b-b44d-2a7ebb07faf8
-- title:
--   Algorithm 2 (least-squares API with lookahead), Assumption 1, Algorithm 3, and the constants $\beta$, $\tau$
-- statement:
--   This module states the algorithms of Sections 3.1 and 3.3 as properties of their runs.
--
--   **Lookahead step** (Step 2 of Algorithms 2 and 3). Given an estimate $J$, a policy $\mu'$ is an $\varepsilon_{LA}$-accurate $H$-step lookahead policy if
--   $$\big\|T^HJ-T_{\mu'}T^{H-1}J\big\|_\infty\le\varepsilon_{LA}.$$
--
--   **Algorithm 2** (least-squares function approximation). Inputs are $J_0$, $m$, $H$, the feature matrix $\Phi$ and evaluation sets $\mathcal D_k\subseteq\mathcal S$. A run is a sequence $(J_k,\mu_k,w_k,\theta_k)_{k\ge0}$ such that for every $k\ge0$:
--
--   1. $\mu_{k+1}$ is an $\varepsilon_{LA}$-accurate $H$-step lookahead policy for $J_k$;
--   2. with the noisy return $\hat J^{\mu_{k+1}}(i)=T^m_{\mu_{k+1}}T^{H-1}(J_k)(i)+w_{k+1}(i)$, the vector $\theta_{k+1}\in\mathbb R^d$ minimises $\sum_{i\in\mathcal D_k}\big((\Phi\theta)(i)-\hat J^{\mu_{k+1}}(i)\big)^2$ (eq. (5));
--   3. $J_{k+1}=\Phi\theta_{k+1}$.
--
--   **Assumption 1.** For each $k\ge0$, $\operatorname{rank}\{\phi(i)\}_{i\in\mathcal D_k}=d$, and for some $\varepsilon_{PE}>0$ the noise satisfies $\|w_k\|_\infty\le\varepsilon_{PE}$ for all $k$.
--
--   **Constants of Theorem 1.**
--   $$\beta=\alpha^{m+H-1}\delta_{FV},\qquad \tau=\frac{\alpha^m+\alpha^{m+H-1}}{1-\alpha}\,\delta_{FV}+\delta_{app}+\delta_{FV}\,\varepsilon_{PE}.$$
--
--   **Algorithm 3** (modified policy iteration with lookahead and time-varying evaluation error $\delta_k$). A run is a sequence $(J_k,\mu_k)_{k\ge0}$ such that for every $k\ge0$, $\mu_{k+1}$ is an $\varepsilon_{LA}$-accurate $H$-step lookahead policy for $J_k$ and $\|J_k-J^{\mu_k}\|_\infty\le\delta_k$.
--
--   Both algorithms are nondeterministic (any accurate lookahead policy, any bounded noise, any minimiser), and every theorem of the mission holds for every run.
--
--   **Formalization Note** The policy $\mu_0$ is not produced by either algorithm; it is left free, so every statement about a run holds for every deterministic $\mu_0$. The noise is written at every state, as Step 3 indexes it ($w_{k+1}$ with $\hat J^{\mu_{k+1}}$); only its entries on $\mathcal D_k$ affect the run, and the paper's convention $w_k(i)=0$ for $i\notin\mathcal D_k$ is replaced by the bound $\|w_k\|_\infty\le\varepsilon_{PE}$ on the whole vector, which constrains nothing the run depends on. For Algorithm 3, the page's Step 3 prints the bound $\|\hat J^{\mu_{k+1}}-J^{\mu_{k+1}}\|_\infty\le\delta_k$; the index used here, $\|J_k-J^{\mu_k}\|_\infty\le\delta_k$, is the one of (15), Proposition 1's sum and Appendix B (with the printed index Proposition 1 would need $\delta_{-1}$). Algorithm 3's representation $J_k=\Phi\theta_k$ is not required: Proposition 1 does not use it, and dropping it lets Proposition 1 apply to Algorithm 2, whose $J_0$ is arbitrary; this generalises Algorithm 3.
-- source:
--   arXiv:2109.13419v7, p. 8, Algorithm 2 and eq. (5); p. 10, Assumption 1; p. 12, Algorithm 3; p. 14, Theorem 1 (β, τ)

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator

namespace LookaheadAPI.LeastSquares

open Matrix

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]

/-- Step 2 of Algorithms 2 and 3 (pp. 8, 12): `μ'` is an `ε_LA`-accurate `H`-step lookahead policy
for the estimate `J`, i.e. `‖T^H J − T_{μ'} T^{H−1} J‖_∞ ≤ ε_LA`. -/
def IsLookahead (M : MDP S A) (H : ℕ) (εLA : ℝ) (J : S → ℝ) (μ' : S → A) : Prop :=
  ‖(bellmanOp M)^[H] J - policyOp M μ' ((bellmanOp M)^[H - 1] J)‖ ≤ εLA

/-- The noisy `m`-step return of Step 3 of Algorithm 2 (p. 8):
`Ĵ^{μ_{k+1}}(i) = T^m_{μ_{k+1}} T^{H−1}(J_k)(i) + w_{k+1}(i)`, written at every state `i`
(only `i ∈ 𝒟_k` enters the algorithm). -/
noncomputable def noisyReturn (M : MDP S A) (m H : ℕ) (J : S → ℝ) (μ' : S → A) (w : S → ℝ) :
    S → ℝ :=
  fun i => (policyOp M μ')^[m] ((bellmanOp M)^[H - 1] J) i + w i

/-- A run of Algorithm 2, "Least-Squares Function Approximation Algorithm" (p. 8), with inputs
`J_0 = J 0`, `m`, `H`, features `Φ` and evaluation sets `𝒟_k = D k`: for every `k ≥ 0`,
Step 2 (`μ_{k+1}` is an `ε_LA`-lookahead policy for `J_k`),
Step 3–4 (`θ_{k+1}` minimises `∑_{i ∈ 𝒟_k} ((Φθ)(i) − Ĵ^{μ_{k+1}}(i))²`, (5)), and
Step 5 (`J_{k+1} = Φ θ_{k+1}`).
The policy `μ 0` and the vectors `θ 0`, `w 0` are not produced by the algorithm and are left free. -/
def IsRunAlg2 {d : ℕ} (M : MDP S A) (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S) (m H : ℕ)
    (εLA : ℝ) (J : ℕ → S → ℝ) (μ : ℕ → S → A) (w : ℕ → S → ℝ) (θ : ℕ → Fin d → ℝ) : Prop :=
  ∀ k : ℕ,
    IsLookahead M H εLA (J k) (μ (k + 1)) ∧
    (∀ θ' : Fin d → ℝ,
      ∑ i ∈ D k, ((Φ *ᵥ θ (k + 1)) i - noisyReturn M m H (J k) (μ (k + 1)) (w (k + 1)) i) ^ 2 ≤
        ∑ i ∈ D k, ((Φ *ᵥ θ') i - noisyReturn M m H (J k) (μ (k + 1)) (w (k + 1)) i) ^ 2) ∧
    J (k + 1) = Φ *ᵥ θ (k + 1)

/-- Assumption 1 (p. 10): for each `k ≥ 0`, `rank {φ(i)}_{i ∈ 𝒟_k} = d` (equivalently
`det (Φ_{𝒟_k}^⊤ Φ_{𝒟_k}) ≠ 0`), and for some `ε_PE > 0` the policy-evaluation noise satisfies
`‖w_k‖_∞ ≤ ε_PE` for all `k`. -/
def Assumption1 {d : ℕ} (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S) (w : ℕ → S → ℝ)
    (εPE : ℝ) : Prop :=
  (∀ k : ℕ, (gram Φ (D k)).det ≠ 0) ∧ 0 < εPE ∧ ∀ k : ℕ, ‖w k‖ ≤ εPE

/-- `β := α^{m+H−1} δ_FV` (Theorem 1, p. 14; (9), p. 13). -/
noncomputable def betaLS {d : ℕ} (M : MDP S A) (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S)
    (m H : ℕ) : ℝ :=
  M.α ^ (m + H - 1) * deltaFV Φ D

/-- `τ := (α^m + α^{m+H−1})/(1 − α) · δ_FV + δ_app + δ_FV ε_PE` (Theorem 1, p. 14). -/
noncomputable def tauLS {d : ℕ} (M : MDP S A) (Φ : Matrix S (Fin d) ℝ) (D : ℕ → Finset S)
    (m H : ℕ) (εPE : ℝ) : ℝ :=
  (M.α ^ m + M.α ^ (m + H - 1)) / (1 - M.α) * deltaFV Φ D + deltaApp M Φ D + deltaFV Φ D * εPE

/-- A run of Algorithm 3, "Modified Policy Iteration With Lookahead And Function Approximation"
(p. 12), with time-varying evaluation-error bounds `δ_k`: for every `k ≥ 0`, `μ_{k+1}` is an
`ε_LA`-lookahead policy for `J_k` (Step 2) and the estimate `J_k` is within `δ_k` of `J^{μ_k}`
(Step 3, with the index of `δ` as in (15) and Appendix B). `μ 0` is an arbitrary deterministic
policy; the feature representation `J_k = Φθ_k` is not required. -/
def IsRunAlg3 (M : MDP S A) (H : ℕ) (εLA : ℝ) (δ : ℕ → ℝ) (J : ℕ → S → ℝ) (μ : ℕ → S → A) :
    Prop :=
  ∀ k : ℕ, IsLookahead M H εLA (J k) (μ (k + 1)) ∧ ‖J k - valueOf M (μ k)‖ ≤ δ k

end LookaheadAPI.LeastSquares



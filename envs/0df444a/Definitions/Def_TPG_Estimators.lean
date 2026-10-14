-- Prove2me | Definitions.Def_TPG_Estimators
-- name    : TPG_Estimators
-- status  : Definition
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:02:14.589432+00:00
-- url     : https://prove2.me/theorems/52e58d75-1d1b-438d-b224-2da15cb1354b
-- title:
--   TPG and reward-corrected estimators, $Q$-values and truncated policy values — eqs. (3), (7), (9)–(11), Appendices D–E
-- statement:
--   Estimators and population quantities of the source, built on the model of `TPG_Model`. Time is $t=0,\dots,T-1$ (the source's $t+1$), and $\mathbb E_\theta$ is expectation under the Bernoulli randomization policy $\pi_\theta$.
--
--   1. **Score** (`score`): $s_\theta(z)=\dfrac{z}{\theta}-\dfrac{1-z}{1-\theta}$ for $z\in\{0,1\}$. At $\theta=1/2$ this is the weight $\mathbf 1\{z=1\}/(1/2)-\mathbf 1\{z=0\}/(1/2)$.
--
--   2. **TPG estimator** (`tpgEst θ T k`), eqs. (3) and (11):
--
--   $$\widehat\tau^{\mathrm{TPG}}_{\theta,k}=\frac1T\sum_{u=0}^{T-1}s_\theta(Z_u)\sum_{t=u}^{\min(u+k,\,T-1)}Y_t .$$
--
--   The estimator $\widehat\tau_k$ of the main text is the case $\theta=1/2$, and $k=0$ is the difference-in-means estimator.
--
--   3. **$Q$-values** (`Env.Q`, `Env.Qk`), eqs. (7) and (10):
--
--   $$Q_\theta^{u}(z)=\sum_{t=u}^{T-1}\mathbb E_\theta[Y_t\mid Z_u=z],\qquad Q_\theta^{u,k}(z)=\sum_{t=u}^{\min(u+k,\,T-1)}\mathbb E_\theta[Y_t\mid Z_u=z].$$
--
--   4. **Truncated policy value** (`Env.truncLaw`, `Env.Jk`), eq. (9). For a reward time $t$, the hypothetical truncated policy uses treatment probability $1/2$ at the times $u<\max(0,t-k)$ and $\theta$ from time $\max(0,t-k)$ on; $\mathcal L_\theta^{t,k}$ is the law of $Y_t$ under it, and
--
--   $$J_k(\theta)=\frac1T\sum_{t<T}\mathbb E_{\mathcal L_\theta^{t,k}}[Y_t].$$
--
--   5. **Matrix form for a general experimental allocation** (`Env.stateDist`, `Env.JkGen`), Appendix D. With $\mu_q^t=\rho^\top P_q^{0\to t}$ the distribution of $X_t$ under $\pi_q$ and $a_t=\max(0,t-k)$,
--
--   $$J_{k,\theta}(q)=\frac1T\sum_{t<T}\mu_\theta^{a_t}\,P_q^{a_t\to t}\,r_q .$$
--
--   6. **Constants** (`Psi`, `Env.rDiffNorm`): $\Psi_k(\gamma)=\sum_{j=0}^{k-2}(j+1)\gamma^j$ with $\Psi_0=\Psi_1=0$, and $\|r_1-r_0\|_\infty=\sup_{x\in S}|r(x,1)-r(x,0)|$.
--
--   7. **Reward-corrected estimator** (`rcWeight`, `rcEst`), Appendix E.1: with $w_\theta(z)=\dfrac{(1-\theta)z}{\theta}+\dfrac{\theta(1-z)}{1-\theta}$,
--
--   $$\widehat\tau^{\mathrm{RC}}_{\theta,k}=\frac1T\sum_{u=0}^{T-1}s_\theta(Z_u)\Bigl[Y_u+\sum_{t=u+1}^{\min(u+k,\,T-1)}w_\theta(Z_t)\,Y_t\Bigr].$$
--
--   These are the objects of Theorem 1 and Propositions 1–6.
--
--   **Formalization Note** Expectations given $\{Z_u=z\}$ are integrals against the conditional measure $\mathbb P_\theta(\cdot\mid Z_u=z)$, which is the zero measure when $\mathbb P_\theta(Z_u=z)=0$; this happens only for $\theta\in\{0,1\}$. The truncated policy of item 4 keeps probability $\theta$ after time $t$, which does not affect the law of $Y_t$. In item 5, $t-k$ is truncated subtraction of natural numbers, i.e. $\max(0,t-k)$. Scores and weights divide by $\theta$ and $1-\theta$ and are used only for $\theta\in(0,1)$.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. eq. (3), p. 11 (TPG estimator); eq. (7), p. 13 (Q-values); eqs. (9)–(10), p. 15 (truncated policy value, truncated Q-values); Appendix D, pp. 31–32, eq. (11) (score, general-θ TPG, J_{k,θ}, Ψ_k); Appendix E.1, p. 33 (reward-corrected estimator).

import Mathlib
import Definitions.Def_TPG_Model

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG

variable {S : Type} [Fintype S]

/-- Bernoulli assignment score `s_θ(z) = z/θ - (1 - z)/(1 - θ)`.
At `θ = 1/2` it is the weight `1{z = 1}/(1/2) - 1{z = 0}/(1/2)`. -/
noncomputable def score (θ : ℝ) (z : Bool) : ℝ :=
  if z then 1 / θ else -(1 / (1 - θ))

/-- Truncated policy gradient (TPG) estimator with truncation size `k` for data collected
under `π_θ`:
`(1/T) ∑_{u < T} s_θ(Z_u) ∑_{u ≤ t ≤ u + k, t < T} Y_t`.
The estimator `τ̂_k` of the main text is `tpgEst (1/2) T k`. -/
noncomputable def tpgEst (θ : ℝ) (T k : ℕ) (ω : Traj S T) : ℝ :=
  (1 / (T : ℝ)) * ∑ u : Fin T, score θ (Z u ω) *
    ∑ t : Fin T, if (u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then Y t ω else 0

/-- `Q`-value of action `z` at time `u` under `π_θ`:
`Q_θ^u(z) = ∑_{u ≤ t < T} E_θ[Y_t | Z_u = z]`. -/
noncomputable def Env.Q [MeasurableSpace S] (E : Env S) (θ : ℝ) (T : ℕ) (u : Fin T)
    (z : Bool) : ℝ :=
  ∑ t : Fin T, if (u : ℕ) ≤ (t : ℕ) then
    ∫ ω, Y t ω ∂(ProbabilityTheory.cond (E.expLaw T θ) {ω | Z u ω = z}) else 0

/-- Truncated `Q`-value of action `z` at time `u` under `π_θ`:
`Q_θ^{u,k}(z) = ∑_{u ≤ t ≤ u + k, t < T} E_θ[Y_t | Z_u = z]`. -/
noncomputable def Env.Qk [MeasurableSpace S] (E : Env S) (θ : ℝ) (T k : ℕ) (u : Fin T)
    (z : Bool) : ℝ :=
  ∑ t : Fin T, if (u : ℕ) ≤ (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then
    ∫ ω, Y t ω ∂(ProbabilityTheory.cond (E.expLaw T θ) {ω | Z u ω = z}) else 0

/-- Law of the trajectory under the hypothetical truncated policy for reward time `t`:
actions at times `u` with `u + k < t` are treatment with probability `1/2`, and actions at
all later times are treatment with probability `θ`. -/
noncomputable def Env.truncLaw [MeasurableSpace S] (E : Env S) (T k t : ℕ) (θ : ℝ) :
    Measure (Traj S T) :=
  E.trajLaw T (fun u => if u + k < t then 1 / 2 else θ)

/-- Truncated policy value function
`J_k(θ) = (1/T) ∑_t E_{L_θ^{t,k}}[Y_t]`. -/
noncomputable def Env.Jk [MeasurableSpace S] (E : Env S) (T k : ℕ) (θ : ℝ) : ℝ :=
  (1 / (T : ℝ)) * ∑ t : Fin T, ∫ ω, Y t ω ∂(E.truncLaw T k (t : ℕ) θ)

/-- Row distribution `μ_q^t = ρᵀ P_q^{0 → t}` of the state at time `t` under `π_q`. -/
noncomputable def Env.stateDist [DecidableEq S] (E : Env S) (q : ℝ) (t : ℕ) : S → ℝ :=
  Matrix.vecMul E.ρ (E.PProd q 0 t)

/-- Hypothetical truncated policy value under the experimental allocation `θ`:
`J_{k,θ}(q) = (1/T) ∑_{t < T} μ_θ^{a_t} P_q^{a_t → t} r_q` with `a_t = max(0, t - k)`. -/
noncomputable def Env.JkGen [DecidableEq S] (E : Env S) (T k : ℕ) (θ q : ℝ) : ℝ :=
  (1 / (T : ℝ)) * ∑ t : Fin T,
    dotProduct
      (Matrix.vecMul (E.stateDist θ ((t : ℕ) - k)) (E.PProd q ((t : ℕ) - k) (t : ℕ)))
      (E.rMix q)

/-- `Ψ_k(γ) = ∑_{j=0}^{k-2} (j + 1) γ^j`, with `Ψ_0 = Ψ_1 = 0`. -/
noncomputable def Psi (k : ℕ) (γ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, if j + 2 ≤ k then ((j : ℝ) + 1) * γ ^ j else 0

/-- `‖r_1 - r_0‖_∞ = sup_x |r(x, 1) - r(x, 0)|`. -/
noncomputable def Env.rDiffNorm (E : Env S) : ℝ :=
  ⨆ x : S, |E.r true x - E.r false x|

/-- Additional importance weight of the reward-corrected estimator,
`w_θ(z) = (1 - θ) z / θ + θ (1 - z) / (1 - θ)`. -/
noncomputable def rcWeight (θ : ℝ) (z : Bool) : ℝ :=
  if z then (1 - θ) / θ else θ / (1 - θ)

/-- Reward-corrected (RC) estimator
`(1/T) ∑_{u < T} s_θ(Z_u) [Y_u + ∑_{u < t ≤ u + k, t < T} w_θ(Z_t) Y_t]`. -/
noncomputable def rcEst (θ : ℝ) (T k : ℕ) (ω : Traj S T) : ℝ :=
  (1 / (T : ℝ)) * ∑ u : Fin T, score θ (Z u ω) *
    (Y u ω + ∑ t : Fin T,
      if (u : ℕ) < (t : ℕ) ∧ (t : ℕ) ≤ (u : ℕ) + k then rcWeight θ (Z t ω) * Y t ω else 0)

end TPG



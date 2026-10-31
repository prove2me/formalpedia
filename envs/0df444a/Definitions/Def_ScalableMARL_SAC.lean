-- Prove2me | Definitions.Def_ScalableMARL_SAC
-- name    : ScalableMARL_SAC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:25.879523+00:00
-- url     : https://prove2.me/theorems/6db47224-3fdb-401d-b94c-faaad4fc1d74
-- title:
--   The Scalable Actor Critic algorithm, its run law, and the constants $C_a$, $C'_a$
-- statement:
--   This module formalizes Algorithm 1 (p. 10) with the critic (14) (p. 14) and the actor (24) (p. 19), the auxiliary sequences (26)–(27) (p. 20), and the constants of Theorem 4 (p. 12).
--
--   1. **Episode.** In each outer iteration an episode $z(0),\dots,z(T)$ of the state-action chain is drawn under the current policy, with $s(0)\sim\pi_0$ and $a(0)\sim\zeta^\theta(\cdot\mid s(0))$; its probability is $P(z(0))\prod_{t<T}P(z(t+1)\mid z(t))$.
--   2. **Critic (14).** With $\alpha_t=h/(t+t_0)$, $\hat Q^0_i=0\in\mathbb R^{\mathcal Z_{N_i^\kappa}}$ and, for $t=1,\dots,T$,
--   $$\hat Q^t_i(z_{N_i^\kappa}(t-1))=(1-\alpha_{t-1})\hat Q^{t-1}_i(z_{N_i^\kappa}(t-1))+\alpha_{t-1}\big(r_i(s_i(t-1),a_i(t-1))+\gamma\hat Q^{t-1}_i(z_{N_i^\kappa}(t))\big),$$
--   with $\hat Q^t_i=\hat Q^{t-1}_i$ at every other local pair.
--   3. **Actor (24).** $\hat g_i=\sum_{t=0}^T\gamma^t\frac1n\sum_{j\in N_i^\kappa}\hat Q^T_j(z_{N_j^\kappa}(t))\,\nabla_{\theta_i}\log\zeta_i^{\theta_i}(a_i(t)\mid s_i(t))$, and $\theta_i(m+1)=\theta_i(m)+\eta_m\hat g_i(m)$ with $\eta_m=\eta/\sqrt{m+1}$.
--   4. **(26)–(27).** $g_i$ is $\hat g_i$ with $\hat Q^T_j$ replaced by the true $Q_j^\theta(s(t),a(t))$, and $h_i(\theta)=\sum_{t=0}^T\mathbb E_{s\sim\pi^\theta_t,a\sim\zeta^\theta(\cdot\mid s)}\big[\gamma^t\frac1n\sum_{j\in N_i^\kappa}Q^\theta_j(s,a)\nabla_{\theta_i}\log\zeta_i^{\theta_i}(a_i\mid s_i)\big]$. $\hat g$, $g$, $h$ are the stacked vectors.
--   5. **Run law.** Along a run of $K$ outer iterations, $\theta(0)$ is given and $\theta(m+1)=\theta(m)+\eta_m\hat g(m)$, where $\hat g(m)$ is computed at $\theta(m)$ from episode $m$; so $\theta(m)$ depends only on episodes $0,\dots,m-1$. The probability of a run is $\prod_{m<K}P_{\theta(m)}(\text{episode } m)$, and the probability of an event is the sum over the runs in it.
--   6. **Constants.** $\bar\epsilon=\frac{4\bar r}{1-\gamma}+2\bar r$,
--   $$C_a(\delta,T)=\frac{6\bar\epsilon}{1-\sqrt\gamma}\sqrt{\frac{\tau h}{\sigma}\Big[\log\frac{2\tau T^2}{\delta}+f(\kappa)\log SA\Big]},\qquad C_a'=\frac{2}{1-\sqrt\gamma}\max\Big(\frac{16\bar\epsilon h\tau}{\sigma},\frac{2\bar r}{1-\gamma}(\tau+t_0)\Big).$$
--
--   **Formalization Note** The critic table of agent $i$ is a function on the local pairs $\mathcal Z_{N_i^\kappa}$ (restricted tuples), not on $\mathcal Z$. `critic … ep k` is $\hat Q^k_i$; its update number $k+1$ uses $\alpha_k=h/(k+t_0)$ and the pairs $z(k)$, $z(k+1)$ of the same episode. An episode is a function `Fin (T+1) → Z`; `thetaRun` is defined for all $m\in\mathbb N$ and stays constant after the $K$ episodes. Probabilities are finite sums of the explicit run probability (the sequential law of the algorithm), so "with probability at least $1-\delta$" is a statement about this sum.
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 10 (Algorithm 1), p. 12 (constants of Theorem 4), p. 14 (eq. (14)), pp. 19–20 (eqs. (24), (26), (27))

import Mathlib
import Definitions.Def_ScalableMARL_NetworkedMDP

namespace ScalableMARL

variable {n : ℕ} {S A : Fin n → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- The critic step size `α_t = h/(t + t₀)` (Algorithm 1, line 6; (14), p. 14). -/
noncomputable def criticStep (h t₀ : ℝ) (t : ℕ) : ℝ := h / (t + t₀)

/-- The actor step size `η_m = η/√(m + 1)` (Algorithm 1, line 12). -/
noncomputable def actorStep (η : ℝ) (m : ℕ) : ℝ := η / Real.sqrt (m + 1)

/-- An episode `z(0), …, z(T)` of the state-action chain. -/
abbrev Episode (S A : Fin n → Type*) (T : ℕ) : Type _ := Fin (T + 1) → ((∀ i, S i) × (∀ i, A i))

/-- `z(t)` of an episode, for `t ≤ T`. -/
def epAt {T : ℕ} (ep : Episode S A T) (t : ℕ) : (∀ i, S i) × (∀ i, A i) :=
  ep ⟨min t T, Nat.lt_succ_of_le (min_le_right t T)⟩

/-- The law of an episode under the fixed policy `θ`: `s(0) ∼ π₀`, `a(0) ∼ ζ^θ(· | s(0))`, and then
the state-action chain, `P(z(0), …, z(T)) = P(z(0)) ∏_{t<T} P(z(t+1) | z(t))`. -/
noncomputable def trajProb (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (θ : pol.Param)
    {T : ℕ} (ep : Episode S A T) : ℝ :=
  initLaw M pol θ (ep 0) * ∏ t : Fin T, chainKernel M pol θ (ep t.castSucc) (ep t.succ)

/-- The probability of an event `E` of episodes under the policy `θ`. -/
noncomputable def trajProbOf (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (θ : pol.Param)
    {T : ℕ} (E : Set (Episode S A T)) : ℝ :=
  ∑ ep, E.indicator (trajProb M pol θ) ep

/-- The critic (TD inner loop) of Algorithm 1, lines 3–9, (14a)–(14b), p. 14, for agent `i`, run on
an episode `ep`: `Q̂⁰_i = 0`, and for `t = 1, …, T`, with `α_{t−1} = h/(t − 1 + t₀)`,
`Q̂^t_i(z_{N_i^κ}(t−1)) = (1 − α_{t−1}) Q̂^{t−1}_i(z_{N_i^κ}(t−1))
  + α_{t−1}(r_i(s_i(t−1), a_i(t−1)) + γ Q̂^{t−1}_i(z_{N_i^κ}(t)))` and `Q̂^t_i = Q̂^{t−1}_i` at
every other local pair. `critic … ep t` is `Q̂^t_i`, indexed by the local pairs `Z_{N_i^κ}`. -/
noncomputable def critic (M : NetMDP n S A) (κ : ℕ) (i : Fin n) (h t₀ : ℝ) {T : ℕ}
    (ep : Episode S A T) : ℕ → LocSA M.G κ i S A → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun x =>
      if x = restrictSA M.G κ i (epAt ep k) then
        (1 - criticStep h t₀ k) * critic M κ i h t₀ ep k x +
          criticStep h t₀ k * (M.r i ((epAt ep k).1 i) ((epAt ep k).2 i) +
            M.γ * critic M κ i h t₀ ep k (restrictSA M.G κ i (epAt ep (k + 1))))
      else critic M κ i h t₀ ep k x

/-- The actor's gradient estimate, Algorithm 1 line 11 and (24), p. 19, block `i`:
`ĝ_i = Σ_{t=0}^T γ^t (1/n) Σ_{j ∈ N_i^κ} Q̂^T_j(z_{N_j^κ}(t)) ∇_{θ_i} log ζ_i^{θ_i}(a_i(t) | s_i(t))`. -/
noncomputable def ghatBlock (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (κ : ℕ) (h t₀ : ℝ)
    (θ : pol.Param) {T : ℕ} (ep : Episode S A T) (i : Fin n) :
    EuclideanSpace ℝ (Fin (pol.d i)) :=
  ∑ t : Fin (T + 1),
    (M.γ ^ (t : ℕ) * (n : ℝ)⁻¹ *
        ∑ j ∈ nbhd M.G κ i, critic M κ j h t₀ ep T (restrictSA M.G κ j (ep t))) •
      pol.logGrad i (θ i) ((ep t).1 i) ((ep t).2 i)

/-- The stacked actor estimate `ĝ = (ĝ₁, …, ĝ_n)` in the parameter space. -/
noncomputable def ghat (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (κ : ℕ) (h t₀ : ℝ)
    (θ : pol.Param) {T : ℕ} (ep : Episode S A T) : pol.Param :=
  WithLp.toLp 2 (fun i => ghatBlock M pol κ h t₀ θ ep i)

/-- (26), p. 20, block `i`: `g_i = Σ_{t=0}^T γ^t (1/n) Σ_{j ∈ N_i^κ} Q_j^θ(s(t), a(t))
∇_{θ_i} log ζ_i^{θ_i}(a_i(t) | s_i(t))`, the estimate with the true Q-functions. -/
noncomputable def gBlock (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (κ : ℕ)
    (θ : pol.Param) {T : ℕ} (ep : Episode S A T) (i : Fin n) :
    EuclideanSpace ℝ (Fin (pol.d i)) :=
  ∑ t : Fin (T + 1),
    (M.γ ^ (t : ℕ) * (n : ℝ)⁻¹ * ∑ j ∈ nbhd M.G κ i, Qi M pol θ j (ep t).1 (ep t).2) •
      pol.logGrad i (θ i) ((ep t).1 i) ((ep t).2 i)

/-- The stacked vector `g = (g₁, …, g_n)` of (26). -/
noncomputable def gvec (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (κ : ℕ)
    (θ : pol.Param) {T : ℕ} (ep : Episode S A T) : pol.Param :=
  WithLp.toLp 2 (fun i => gBlock M pol κ θ ep i)

/-- (27), p. 20, block `i`: `h_i(θ) = Σ_{t=0}^T E_{s∼π_t^θ, a∼ζ^θ(·|s)}[γ^t (1/n)
Σ_{j ∈ N_i^κ} Q_j^θ(s, a) ∇_{θ_i} log ζ_i^{θ_i}(a_i | s_i)]`. -/
noncomputable def hBlock (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (κ T : ℕ)
    (θ : pol.Param) (i : Fin n) : EuclideanSpace ℝ (Fin (pol.d i)) :=
  ∑ t ∈ Finset.range (T + 1), ∑ s, ∑ a,
    (stateDist M pol θ t s * pol.joint θ s a *
        (M.γ ^ t * (n : ℝ)⁻¹ * ∑ j ∈ nbhd M.G κ i, Qi M pol θ j s a)) •
      pol.logGrad i (θ i) (s i) (a i)

/-- The stacked vector `h(θ) = (h₁(θ), …, h_n(θ))` of (27); `h(m) = h(θ(m))`. -/
noncomputable def hvec (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (κ T : ℕ)
    (θ : pol.Param) : pol.Param :=
  WithLp.toLp 2 (fun i => hBlock M pol κ T θ i)

/-- The actor iterates of Algorithm 1 along a run `ω` of `K` episodes:
`θ(0) = θ₀` and `θ(m+1) = θ(m) + η_m ĝ(m)`, where `ĝ(m)` is computed at `θ(m)` from episode `m`
(line 12). `θ(m)` depends only on the episodes `0, …, m − 1`; past `K` it stays constant. -/
noncomputable def thetaRun (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (κ : ℕ)
    (h t₀ η : ℝ) (θ₀ : pol.Param) {K T : ℕ} (ω : Fin K → Episode S A T) : ℕ → pol.Param
  | 0 => θ₀
  | m + 1 =>
      if hm : m < K then
        thetaRun M pol κ h t₀ η θ₀ ω m +
          actorStep η m • ghat M pol κ h t₀ (thetaRun M pol κ h t₀ η θ₀ ω m) (ω ⟨m, hm⟩)
      else thetaRun M pol κ h t₀ η θ₀ ω m

/-- The law of a run of SAC (Algorithm 1) over `K` outer iterations: episode `m` is drawn, with a
fresh `s(0) ∼ π₀`, under the policy `θ(m)` computed from the earlier episodes, so
`P(ω) = ∏_{m<K} P_{θ(m)}(ω_m)`. -/
noncomputable def runProb (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (κ : ℕ)
    (h t₀ η : ℝ) (θ₀ : pol.Param) {K T : ℕ} (ω : Fin K → Episode S A T) : ℝ :=
  ∏ m : Fin K, trajProb M pol (thetaRun M pol κ h t₀ η θ₀ ω m) (ω m)

/-- The probability of an event `E` of runs of SAC over `K` outer iterations. -/
noncomputable def runProbOf (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (κ : ℕ)
    (h t₀ η : ℝ) (θ₀ : pol.Param) {K T : ℕ} (E : Set (Fin K → Episode S A T)) : ℝ :=
  ∑ ω, E.indicator (runProb M pol κ h t₀ η θ₀) ω

/-- `ε̄ = 4 r̄/(1 − γ) + 2 r̄` (Theorem 4, p. 12). -/
noncomputable def epsBar (γ rbar : ℝ) : ℝ := 4 * rbar / (1 - γ) + 2 * rbar

/-- `C_a(δ, T) = (6 ε̄/(1 − √γ)) √((τ h/σ)[log(2τT²/δ) + f(κ) log SA])` (Theorem 4, p. 12),
with `f(κ) = fκ`, `S = Sb`, `A = Ab`. -/
noncomputable def Ca (γ rbar τ h σ fκ Sb Ab δ T : ℝ) : ℝ :=
  6 * epsBar γ rbar / (1 - Real.sqrt γ) *
    Real.sqrt (τ * h / σ * (Real.log (2 * τ * T ^ 2 / δ) + fκ * Real.log (Sb * Ab)))

/-- `C'_a = (2/(1 − √γ)) max(16 ε̄ h τ/σ, (2 r̄/(1 − γ))(τ + t₀))` (Theorem 4, p. 12). -/
noncomputable def Ca' (γ rbar τ h σ t₀ : ℝ) : ℝ :=
  2 / (1 - Real.sqrt γ) * max (16 * epsBar γ rbar * h * τ / σ) (2 * rbar / (1 - γ) * (τ + t₀))

end ScalableMARL



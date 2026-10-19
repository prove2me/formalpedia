-- Prove2me | Definitions.Def_OffPolicyDRL_CrossFit_MDP
-- name    : OffPolicyDRL_CrossFit_MDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:01.3002+00:00
-- url     : https://prove2.me/theorems/4adba922-4a53-466f-b46e-89a0c4605e49
-- title:
--   Time-invariant MDP on measurable spaces: state–action chain, marginals, discounted visitation, q- and v-functions, policy value (Sec. 1.2, pp. 4–6)
-- statement:
--   Let $S$ (states) and $A$ (actions) be measurable spaces. A **time-invariant Markov decision process** is given by a transition kernel $p(s' \mid s,a)$ and a reward kernel $p(r \mid s,a)$ on $\mathbb R$. It is **bounded by** $R_{\max} \ge 0$ when both kernels are Markov and every reward lies in $[0,R_{\max}]$.
--
--   Fix a policy $\pi(a\mid s)$ (a kernel from $S$ to $A$), an initial law $\nu_0$ and a discount factor $\gamma$. The following objects are defined.
--
--   1. The mean reward $\bar r(s,a) = \int r\, p(dr\mid s,a)$.
--   2. The one-step state–action kernel: from $(s,a)$ draw $s' \sim p(\cdot\mid s,a)$, then $a' \sim \pi(\cdot\mid s')$; and its $k$-step power ($k=0$ is the identity).
--   3. The marginal law $p^{(t)}_\pi$ of $(s_t,a_t)$ along a trajectory with $s_0\sim\nu_0$, $a_0\sim\pi(\cdot\mid s_0)$, and its state marginal $p^{(t)}_\pi(s_t)$.
--   4. The policy value
--   $$\rho^\pi=\lim_{T\to\infty}\Big(\sum_{t=0}^T\gamma^t\Big)^{-1}\sum_{t=0}^T\gamma^t\,\mathbb E_{p_\pi}[r_t],\qquad \mathbb E_{p_\pi}[r_t]=\mathbb E\big[\bar r(s_t,a_t)\big].$$
--   5. The $\gamma$-discounted average visitation frequency $p^{(\infty)}_{\pi,\gamma}=(1-\gamma)\sum_{t\ge0}\gamma^t p^{(t)}_\pi(s_t)$.
--   6. The q-function $q(s,a)=\sum_{k\ge0}\gamma^k\,\mathbb E[r_k\mid s_0=s,a_0=a]$. For any $q'$ the induced state function is $v'(s)=\int q'(s,a)\,\pi(da\mid s)$; in particular the v-function is $v(s)=\int q(s,a)\,\pi(da\mid s)$.
--
--   These are the general objects of Section 1.2 of the paper, for an arbitrary policy and initial law. The off-policy evaluation model instantiates them at the target policy.
--
--   **Formalization Note** The trajectory law itself is not built. Every quantity the paper uses is an expectation of a function of one $(s_t,a_t)$, and its law is the $t$-step marginal computed by kernel composition. The paper defines $p^{(\infty)}_{\pi,\gamma}$ as the limit of the normalized averages $(\sum_{t\le T}\gamma^t)^{-1}\sum_{t\le T}\gamma^t p^{(t)}_\pi$. Here it is the limiting measure itself, the series $(1-\gamma)\sum_t\gamma^t p^{(t)}_\pi$; for $0\le\gamma<1$ the averages converge to it in total variation. $\rho^\pi$ uses `limUnder`, whose junk value only arises if the limit fails to exist (it exists for bounded rewards). The tsum defining $q$ is $0$ if the series is not summable (it is summable for bounded rewards and $\gamma<1$).
-- source:
--   Kallus & Uehara, Efficiently Breaking the Curse of Horizon in Off-Policy Evaluation with Double Reinforcement Learning, arXiv:1909.05850v6, Section 1.2, pp. 4–6 (MDP, trajectory density, p^{(t)}_π, p^{(∞)}_{π,γ}, ρ^π_T, ρ^π, q, v)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace OffPolicyDRL.CrossFit

/-- A time-invariant Markov decision process on a measurable state space `S` and a measurable
action space `A` (Kallus–Uehara, Sec. 1.2, p. 4): a transition kernel `P` giving the law of the
next state `s′` after action `a` in state `s`, and a reward kernel `Rw` giving the law of the
immediate reward `r`. -/
structure MDP (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] where
  /-- transition distribution `p(s′ | s, a)` -/
  P : Kernel (S × A) S
  /-- reward distribution `p(r | s, a)` -/
  Rw : Kernel (S × A) ℝ

namespace MDP

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : MDP S A)

/-- Both kernels are Markov and every reward lies in `[0, Rmax]` (Sec. 1.2: `R ⊂ [0, Rmax]`). -/
structure IsBounded (Rmax : ℝ) : Prop where
  rmax_nonneg : 0 ≤ Rmax
  markov_P : IsMarkovKernel M.P
  markov_Rw : IsMarkovKernel M.Rw
  reward_mem : ∀ x, M.Rw x (Set.Icc 0 Rmax)ᶜ = 0

/-- Mean immediate reward `E[r | s, a]`. -/
noncomputable def meanReward (x : S × A) : ℝ := ∫ r, r ∂(M.Rw x)

/-- One step of the state–action chain under the policy `π`: from `(s, a)` draw
`s′ ∼ p(· | s, a)` and then `a′ ∼ π(· | s′)`. -/
noncomputable def stepKernel (π : Kernel S A) : Kernel (S × A) (S × A) :=
  (Kernel.id ×ₖ π) ∘ₖ M.P

/-- The `k`-step state–action kernel under `π` (`k = 0` is the identity). -/
noncomputable def stepKernelPow (π : Kernel S A) : ℕ → Kernel (S × A) (S × A)
  | 0 => Kernel.id
  | k + 1 => M.stepKernel π ∘ₖ stepKernelPow π k

/-- The marginal law `p^{(t)}_π(s_t, a_t)` of `(s_t, a_t)` along a trajectory started at
`s_0 ∼ ν0`, `a_0 ∼ π(· | s_0)`. -/
noncomputable def margSA (ν0 : Measure S) (π : Kernel S A) (t : ℕ) : Measure (S × A) :=
  M.stepKernelPow π t ∘ₘ (ν0 ⊗ₘ π)

/-- The marginal law `p^{(t)}_π(s_t)` of the state `s_t`. -/
noncomputable def margS (ν0 : Measure S) (π : Kernel S A) (t : ℕ) : Measure S :=
  (M.margSA ν0 π t).fst

/-- The normalized discounted value up to horizon `T`,
`ρ^π_T = (∑_{t ≤ T} γ^t)⁻¹ E_{p_π}[∑_{t ≤ T} γ^t r_t]`, with `E[r_t] = E[E[r | s_t, a_t]]`. -/
noncomputable def policyValueT (γ : ℝ) (ν0 : Measure S) (π : Kernel S A) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range (T + 1), γ ^ t)⁻¹ *
    ∑ t ∈ Finset.range (T + 1), γ ^ t * ∫ x, M.meanReward x ∂(M.margSA ν0 π t)

/-- The policy value `ρ^π = lim_{T → ∞} ρ^π_T` (p. 5). `limUnder` returns a junk value if the
limit does not exist; under `IsBounded` and `0 ≤ γ < 1` it exists. -/
noncomputable def policyValue (γ : ℝ) (ν0 : Measure S) (π : Kernel S A) : ℝ :=
  limUnder atTop (M.policyValueT γ ν0 π)

/-- The `γ`-discounted average visitation frequency `p^{(∞)}_{π,γ}`, as the measure
`(1 - γ) ∑_t γ^t p^{(t)}_π`; it is the (total-variation) limit of the normalized averages
`(∑_{t ≤ T} γ^t)⁻¹ ∑_{t ≤ T} γ^t p^{(t)}_π` of p. 5. -/
noncomputable def discVisitation (γ : ℝ) (ν0 : Measure S) (π : Kernel S A) : Measure S :=
  ENNReal.ofReal (1 - γ) • Measure.sum (fun t => ENNReal.ofReal (γ ^ t) • M.margS ν0 π t)

/-- The q-function `q(s, a) = E_{p_π}[∑_k γ^k r_k | s_0 = s, a_0 = a]` (p. 6), as the series
`∑_k γ^k E[r_k | s_0, a_0]`. -/
noncomputable def qFun (γ : ℝ) (π : Kernel S A) (x : S × A) : ℝ :=
  ∑' k : ℕ, γ ^ k * ∫ y, M.meanReward y ∂(M.stepKernelPow π k x)

/-- The state function `v′(s) = E_{a ∼ π(· | s)}[q′(s, a)]` induced by any `q′`. -/
noncomputable def vOf (π : Kernel S A) (q' : S × A → ℝ) (s : S) : ℝ := ∫ a, q' (s, a) ∂(π s)

/-- The v-function `v(s) = E_{p_π}[∑_k γ^k r_k | s_0 = s] = E_{a ∼ π(· | s)}[q(s, a)]` (p. 6). -/
noncomputable def vFun (γ : ℝ) (π : Kernel S A) (s : S) : ℝ := vOf π (M.qFun γ π) s

end MDP

end OffPolicyDRL.CrossFit



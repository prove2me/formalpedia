-- Prove2me | Definitions.Def_ScalableMARL_Assumptions
-- name    : ScalableMARL_Assumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:11.248037+00:00
-- url     : https://prove2.me/theorems/d0ea8b0d-9422-4311-9ea1-d2b5fe4b77ec
-- title:
--   Assumptions 1–4 of Scalable Actor Critic
-- statement:
--   The four assumptions of §3.3 (pp. 11–12), for the networked MDP and a class of localized policies.
--
--   1. **Assumption 1 (bounded reward and space sizes).** $0\le r_i(s_i,a_i)\le\bar r$ for all $i,s_i,a_i$, and $|\mathcal S_i|\le S$, $|\mathcal A_i|\le A$ for all $i$.
--   2. **Assumption 2 (exponential decay).** The $(c,\rho)$-exponential decay property (Definition 1) holds, at the algorithm's hop count $\kappa$, for some $\rho\le\gamma$.
--   3. **Assumption 3 (sufficient local exploration).** For an integer $\tau\ge1$ and $\sigma\in(0,1)$: under any fixed policy $\theta$, from any state-action pair $(s(1),a(1))=z$, for every $i$ and every local pair $x\in\mathcal Z_{N_i^\kappa}$,
--   $$\mathbb P\big(z_{N_i^\kappa}(\tau)=x\mid z(1)=z\big)\ge\sigma .$$
--   4. **Assumption 4 (bounded and Lipschitz gradients).** $\|\nabla_{\theta_i}\log\zeta_i^{\theta_i}(a_i\mid s_i)\|\le L_i$ for all $i,a_i,s_i,\theta_i$; $L=\sqrt{\sum_i L_i^2}$; and $\nabla J$ is $L'$-Lipschitz: $\|\nabla J(\theta)-\nabla J(\theta')\|\le L'\|\theta-\theta'\|$.
--
--   Theorem 4 assumes all four; the lemmas of its proof assume the parts they use.
--
--   **Formalization Note** $S$ and $A$ are real numbers (they enter only through $\log SA$). The probability in Assumption 3 is the mass that the $(\tau-1)$-step law of the state-action chain started at $z$ puts on $\{z' : z'_{N_i^\kappa}=x\}$: the chain is time homogeneous and $z(1)\to z(\tau)$ is $\tau-1$ transitions. Assumption 4 is split into `LogGradBound` (first sentence) and `GradLipschitz` (last sentence, with a Lipschitz constant $L'\ge0$); "as a result $\|\nabla_\theta\log\zeta^\theta(a\mid s)\|\le L$" on the page is a consequence, not part of the assumption. Assumption 2 is $(c,\rho)$-exponential decay plus $\rho\le\gamma$; the positivity of $c$ and $\rho$ is assumed separately where a statement takes their logarithm.
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, pp. 11–12, Assumptions 1–4

import Mathlib
import Definitions.Def_ScalableMARL_NetworkedMDP

namespace ScalableMARL

variable {n : ℕ} {S A : Fin n → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- Assumption 1 (p. 11), bounded reward and state/action space size:
`0 ≤ r_i(s_i, a_i) ≤ r̄` for all `i, s_i, a_i`, and `|S_i| ≤ S`, `|A_i| ≤ A` for all `i`
(here `S`, `A` are the reals `Sb`, `Ab`). -/
def Assumption1 (M : NetMDP n S A) (rbar Sb Ab : ℝ) : Prop :=
  (∀ i s a, 0 ≤ M.r i s a ∧ M.r i s a ≤ rbar) ∧
  (∀ i, (Fintype.card (S i) : ℝ) ≤ Sb) ∧ (∀ i, (Fintype.card (A i) : ℝ) ≤ Ab)

/-- Assumption 2 (p. 12), exponential decay: the `(c, ρ)`-exponential decay property
(Definition 1) holds at the algorithm's hop count `κ`, for some `ρ ≤ γ`. -/
def Assumption2 (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (c ρ : ℝ) (κ : ℕ) : Prop :=
  ExpDecay M pol c ρ κ ∧ ρ ≤ M.γ

/-- Assumption 3 (p. 12), sufficient local exploration: `τ ≥ 1` is an integer and `σ ∈ (0, 1)`,
and under any fixed policy `θ`, from any state-action pair `z = (s(1), a(1))`, for every agent `i`
and every local pair `x ∈ Z_{N_i^κ}`, `P(z_{N_i^κ}(τ) = x | z(1) = z) ≥ σ`; that is, the
`(τ − 1)`-step law of the state-action chain from `z` puts mass at least `σ` on `{z' : z'_{N_i^κ} = x}`. -/
def Assumption3 (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (κ τ : ℕ) (σ : ℝ) : Prop :=
  1 ≤ τ ∧ 0 < σ ∧ σ < 1 ∧
    ∀ (θ : pol.Param) (z : (∀ i, S i) × (∀ i, A i)) (i : Fin n) (x : LocSA M.G κ i S A),
      σ ≤ ∑ z' ∈ Finset.univ.filter (fun z' => restrictSA M.G κ i z' = x),
        chainLaw M pol θ z (τ - 1) z'

/-- Assumption 4 (p. 12), first part: `‖∇_{θ_i} log ζ_i^{θ_i}(a_i | s_i)‖ ≤ L_i` for all
`i, a_i, s_i, θ_i`. -/
def LogGradBound (pol : LocalPolicyClass n S A) (L : Fin n → ℝ) : Prop :=
  ∀ i x s a, ‖pol.logGrad i x s a‖ ≤ L i

/-- `L = √(Σ_i L_i²)` (Assumption 4, p. 12). -/
noncomputable def Lnorm (L : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, L i ^ 2)

/-- Assumption 4 (p. 12), second part: `∇J` is `L'`-Lipschitz on the parameter space with its
Euclidean norm, `‖∇J(θ) − ∇J(θ')‖ ≤ L' ‖θ − θ'‖`, with a Lipschitz constant `L' ≥ 0`. -/
def GradLipschitz (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (L' : ℝ) : Prop :=
  0 ≤ L' ∧ ∀ θ θ' : pol.Param, ‖gradient (J M pol) θ - gradient (J M pol) θ'‖ ≤ L' * ‖θ - θ'‖

end ScalableMARL



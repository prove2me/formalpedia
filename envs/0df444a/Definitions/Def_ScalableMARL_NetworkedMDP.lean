-- Prove2me | Definitions.Def_ScalableMARL_NetworkedMDP
-- name    : ScalableMARL_NetworkedMDP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:46:29.639288+00:00
-- url     : https://prove2.me/theorems/731c6dbd-d012-4df1-91b1-ab5cf647bbb3
-- title:
--   Networked MDP, localized policies, Q-functions $Q_i^\theta$, objective $J(\theta)$ and the $(c,\rho)$-exponential decay property
-- statement:
--   This module sets up the model of §2.1 and the objects of §2.3 and §3.1 of Qu, Wierman and Li.
--
--   1. **Networked MDP.** There are $n$ agents $\mathcal N=\{1,\dots,n\}$ on an undirected graph $G=(\mathcal N,\mathcal E)$. For $\kappa\ge 0$, the **κ-hop neighbourhood** $N_i^\kappa$ is the set of agents at graph distance at most $\kappa$ from $i$ (it contains $i$), $N_i=N_i^1$, and $f(\kappa)=\max_i|N_i^\kappa|$. Agent $i$ has a finite local state set $\mathcal S_i$ and a finite local action set $\mathcal A_i$; the global state is $s=(s_1,\dots,s_n)\in\mathcal S=\mathcal S_1\times\dots\times\mathcal S_n$ and the global action $a\in\mathcal A=\mathcal A_1\times\dots\times\mathcal A_n$. The next state is drawn from the product kernel (1)
--   $$P(s(t+1)\mid s(t),a(t))=\prod_{i=1}^n P\big(s_i(t+1)\mid s_{N_i}(t),a_i(t)\big).$$
--   Agent $i$ receives the reward $r_i(s_i,a_i)$, the global reward is $r(s,a)=\frac1n\sum_i r_i(s_i,a_i)$, the initial state is drawn from $\pi_0$, and $\gamma\in(0,1)$ is the discount factor. The data are **valid** when all local kernels and $\pi_0$ are probability distributions and $0<\gamma<1$.
--   2. **Localized policies.** Agent $i$ has a parameter $\theta_i\in\mathbb R^{d_i}$ and a conditional distribution $\zeta_i^{\theta_i}(\cdot\mid s_i)$ on $\mathcal A_i$; the joint policy is $\zeta^\theta(a\mid s)=\prod_i\zeta_i^{\theta_i}(a_i\mid s_i)$ with $\theta=(\theta_1,\dots,\theta_n)$, normed by the Euclidean norm of the whole tuple. $\nabla_{\theta_i}\log\zeta_i^{\theta_i}(a_i\mid s_i)$ is the gradient in $\theta_i$.
--   3. **Values.** $Q_i^\theta(s,a)=\mathbb E\big[\sum_{t\ge0}\gamma^t r_i(s_i(t),a_i(t))\mid s(0)=s,a(0)=a\big]$ and $Q^\theta(s,a)$ the same for $r$ (eq. (7)); $J(\theta)=\mathbb E_{s\sim\pi_0}\mathbb E\big[\sum_{t\ge0}\gamma^t r(s(t),a(t))\mid s(0)=s\big]$ (eq. (2)); $\pi_t^\theta$ is the law of $s(t)$ and $\pi^\theta(s)=(1-\gamma)\sum_{t\ge0}\gamma^t\pi_t^\theta(s)$ the discounted visitation distribution (Lemma 1).
--   4. **The state-action chain.** Under $\theta$, $z(t)=(s(t),a(t))$ is a Markov chain on $\mathcal Z=\mathcal S\times\mathcal A$: $s(t+1)$ is drawn from (1) and then $a(t+1)\sim\zeta^\theta(\cdot\mid s(t+1))$; $z(0)$ has $s(0)\sim\pi_0$, $a(0)\sim\zeta^\theta(\cdot\mid s(0))$. The module defines its kernel, initial law and $t$-step law.
--   5. **Local pairs.** $z_{N_i^\kappa}=(s_{N_i^\kappa},a_{N_i^\kappa})\in\mathcal Z_{N_i^\kappa}$ is the restriction of $z$ to the κ-hop neighbourhood.
--   6. **Definition 1 ((c,ρ)-exponential decay).** For every localized policy $\theta$, every $i$, and all $z,z'\in\mathcal Z$ that agree on $N_i^\kappa$,
--   $$|Q_i^\theta(z)-Q_i^\theta(z')|\le c\rho^{\kappa+1}.$$
--   7. **Truncated Q-functions (9)–(10).** $\hat Q_i^\theta(z_{N_i^\kappa})=\sum_{z_{N_{-i}^\kappa}}w_i(z_{N_{-i}^\kappa};z_{N_i^\kappa})\,Q_i^\theta(z_{N_i^\kappa},z_{N_{-i}^\kappa})$ for nonnegative weights summing to one for every $z_{N_i^\kappa}$.
--
--   These are the objects in which Lemma 1, Lemma 3, Lemma 17 and all results on the SAC algorithm are stated.
--
--   **Formalization Note** Agents are `Fin n`, and graph distance is `SimpleGraph.edist` (infinite for unreachable agents). The local kernel of agent $i$ takes the restricted tuple $s_{N_i}$ as argument, so the locality of (1) is built into its type. $Q_i^\theta$ and $Q^\theta$ are the published finite-MDP `QFunction` of the global MDP (kernel (1), policy $\zeta^\theta$), i.e. $r_i(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V(s')$ with $V$ the discounted series of expected rewards (the published `PolicyValue`); for finite valid MDPs this is the expectation (7). $J$ averages `PolicyValue` over $\pi_0$, and $\pi_t^\theta$ averages the published `OccupationDist`. The parameter space is `PiLp 2 (fun i => EuclideanSpace ℝ (Fin (d i)))`, whose norm is the Euclidean norm of the whole vector. In a truncated Q-function the weights are indexed by the global pairs $z$ with $z_{N_i^\kappa}=x$, which are in bijection with the tuples $z_{N_{-i}^\kappa}$. Validity of the data and of the policies, and the positivity and differentiability of $\zeta_i$ needed for $\nabla\log\zeta_i$, are separate predicates, assumed by the theorems that need them.
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 4 (§2.1, eqs. (1)–(2)), p. 7 (eq. (7)), p. 8 (Lemma 1, Definition 1), p. 9 (eqs. (9)–(10))

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_OccupationDist
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction

namespace ScalableMARL

open FoundationsML.ReinforcementLearning

/-- The κ-hop neighbourhood `N_i^κ = {j : dist_G(i, j) ≤ κ}` of agent `i` in the undirected graph
`G` on the agents `N = {1, …, n}` (Qu, Wierman & Li, *Scalable Reinforcement Learning for
Multi-Agent Networked Systems*, arXiv:1912.02906v3, §2.1, p. 4). It contains `i` itself; `N_i = N_i^1`.

**Formalization Note.** The graph distance is `SimpleGraph.edist` (`⊤` for unreachable agents, so
they are never in the neighbourhood); agents are `Fin n`. -/
noncomputable def nbhd {n : ℕ} (G : SimpleGraph (Fin n)) (κ : ℕ) (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => G.edist i j ≤ (κ : ℕ∞))

/-- `f(κ) = max_i |N_i^κ|`, the size of the largest κ-hop neighbourhood (p. 4 and p. 12). -/
noncomputable def maxNbhdSize {n : ℕ} (G : SimpleGraph (Fin n)) (κ : ℕ) : ℕ :=
  Finset.univ.sup (fun i => (nbhd G κ i).card)

/-- The networked MDP of §2.1 (p. 4): an undirected graph `G` on the agents `Fin n`; agent `i`
has a finite local state set `S i` and a finite local action set `A i`; the local transition
kernel `P i (s_{N_i}) (a_i) (s_i')` gives the law of `s_i(t+1)` from the states of the
1-hop neighbourhood `N_i` (including `i`) and the own action `a_i(t)`; `r i s_i a_i` is the
local stage reward; `π₀` is the initial state distribution on `S = Π_i S_i`; `γ` is the
discount factor. -/
structure NetMDP (n : ℕ) (S A : Fin n → Type*) where
  /-- the undirected interaction graph `G = (N, E)` -/
  G : SimpleGraph (Fin n)
  /-- local kernels `P(s_i(t+1) | s_{N_i}(t), a_i(t))` -/
  P : ∀ i : Fin n, (∀ j : nbhd G 1 i, S j) → A i → S i → ℝ
  /-- local rewards `r_i(s_i, a_i)` -/
  r : ∀ i : Fin n, S i → A i → ℝ
  /-- initial state distribution `π₀` on `S = S₁ × ⋯ × S_n` -/
  π₀ : (∀ i, S i) → ℝ
  /-- discount factor `γ` -/
  γ : ℝ

variable {n : ℕ} {S A : Fin n → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- The standing conditions on the data (p. 4, p. 2): every local kernel is a probability
distribution on `S i`, `π₀` is a probability distribution on `S`, and `γ ∈ (0, 1)`. -/
def NetMDP.Valid (M : NetMDP n S A) : Prop :=
  (∀ i x a s', 0 ≤ M.P i x a s') ∧ (∀ i x a, ∑ s', M.P i x a s' = 1) ∧
  (∀ s, 0 ≤ M.π₀ s) ∧ ∑ s, M.π₀ s = 1 ∧ 0 < M.γ ∧ M.γ < 1

/-- The global transition kernel (1): `P(s' | s, a) = ∏_i P(s'_i | s_{N_i}, a_i)`. -/
noncomputable def NetMDP.globalP (M : NetMDP n S A) (s : ∀ i, S i) (a : ∀ i, A i)
    (s' : ∀ i, S i) : ℝ :=
  ∏ i, M.P i (fun j => s j) (a i) (s' i)

/-- The local reward of agent `i` read on global state-action pairs, `(s, a) ↦ r_i(s_i, a_i)`. -/
def NetMDP.localReward (M : NetMDP n S A) (i : Fin n) (s : ∀ i, S i) (a : ∀ i, A i) : ℝ :=
  M.r i (s i) (a i)

/-- The global stage reward `r(s, a) = (1/n) Σ_i r_i(s_i, a_i)` (p. 4). -/
noncomputable def NetMDP.reward (M : NetMDP n S A) (s : ∀ i, S i) (a : ∀ i, A i) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, M.r i (s i) (a i)

/-- A class of localized policies (p. 4): agent `i` has a parameter `θ_i ∈ ℝ^{d_i}` and a
conditional law `ζ_i^{θ_i}(a_i | s_i)` on its local action given its local state. -/
structure LocalPolicyClass (n : ℕ) (S A : Fin n → Type*) where
  /-- parameter dimensions `d_i` -/
  d : Fin n → ℕ
  /-- `ζ i θ_i s_i a_i = ζ_i^{θ_i}(a_i | s_i)` -/
  ζ : ∀ i, EuclideanSpace ℝ (Fin (d i)) → S i → A i → ℝ

/-- The parameter space of `θ = (θ₁, …, θ_n)`, with the Euclidean norm on the whole tuple. -/
abbrev LocalPolicyClass.Param (pol : LocalPolicyClass n S A) : Type :=
  PiLp 2 (fun i => EuclideanSpace ℝ (Fin (pol.d i)))

/-- Each `ζ_i^{θ_i}(· | s_i)` is a probability distribution on `A i`. -/
def LocalPolicyClass.IsDistribution (pol : LocalPolicyClass n S A) : Prop :=
  ∀ i x s, (∀ a, 0 ≤ pol.ζ i x s a) ∧ ∑ a, pol.ζ i x s a = 1

/-- `ζ_i^{θ_i}(a_i | s_i) > 0` and `θ_i ↦ ζ_i^{θ_i}(a_i | s_i)` is differentiable, for all
`i, a_i, s_i` — what Assumption 4 (p. 12) presupposes for `∇_{θ_i} log ζ_i^{θ_i}(a_i | s_i)`
to exist. -/
def LocalPolicyClass.PositiveDifferentiable (pol : LocalPolicyClass n S A) : Prop :=
  (∀ i x s a, 0 < pol.ζ i x s a) ∧ ∀ i s a, Differentiable ℝ (fun x => pol.ζ i x s a)

/-- The joint policy `ζ^θ(a | s) = ∏_i ζ_i^{θ_i}(a_i | s_i)` (p. 4). -/
noncomputable def LocalPolicyClass.joint (pol : LocalPolicyClass n S A) (θ : pol.Param)
    (s : ∀ i, S i) (a : ∀ i, A i) : ℝ :=
  ∏ i, pol.ζ i (θ i) (s i) (a i)

/-- `∇_{θ_i} log ζ_i^{θ_i}(a_i | s_i)` at `θ_i = x`. -/
noncomputable def LocalPolicyClass.logGrad (pol : LocalPolicyClass n S A) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin (pol.d i))) (s : S i) (a : A i) : EuclideanSpace ℝ (Fin (pol.d i)) :=
  gradient (fun y => Real.log (pol.ζ i y s a)) x

/-- `Q_i^θ(s, a) = E[Σ_{t≥0} γ^t r_i(s_i(t), a_i(t)) | s(0) = s, a(0) = a]`, (7), p. 7: the
published finite-MDP `QFunction` of the global MDP (kernel (1), joint policy `ζ^θ`) with the
reward `r_i`. -/
noncomputable def Qi (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (θ : pol.Param)
    (i : Fin n) (s : ∀ i, S i) (a : ∀ i, A i) : ℝ :=
  QFunction (pol.joint θ) M.globalP (M.localReward i) M.γ s a

/-- `Q^θ(s, a) = E[Σ_{t≥0} γ^t r(s(t), a(t)) | s(0) = s, a(0) = a]`, (7), p. 7, for the global
reward `r`. -/
noncomputable def Qglob (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (θ : pol.Param)
    (s : ∀ i, S i) (a : ∀ i, A i) : ℝ :=
  QFunction (pol.joint θ) M.globalP M.reward M.γ s a

/-- The objective (2), p. 4: `J(θ) = E_{s∼π₀} E[Σ_{t≥0} γ^t r(s(t), a(t)) | s(0) = s]`. -/
noncomputable def J (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (θ : pol.Param) : ℝ :=
  ∑ s, M.π₀ s * PolicyValue (pol.joint θ) M.globalP M.reward M.γ s

/-- `π_t^θ(s)`, the law of `s(t)` under the fixed policy `θ` with `s(0) ∼ π₀` (Lemma 1, p. 8). -/
noncomputable def stateDist (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (θ : pol.Param)
    (t : ℕ) (s : ∀ i, S i) : ℝ :=
  ∑ s₀, M.π₀ s₀ * OccupationDist (pol.joint θ) M.globalP s₀ t s

/-- The discounted state visitation distribution `π^θ(s) = (1 − γ) Σ_{t≥0} γ^t π_t^θ(s)`
(Lemma 1, p. 8). -/
noncomputable def visitation (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (θ : pol.Param)
    (s : ∀ i, S i) : ℝ :=
  (1 - M.γ) * ∑' t : ℕ, M.γ ^ t * stateDist M pol θ t s

/-- The transition kernel of the state-action chain `z(t) = (s(t), a(t))` on `Z = S × A` under
`θ`: `s(t+1)` is drawn from (1) and then `a(t+1) ∼ ζ^θ(· | s(t+1))`. -/
noncomputable def chainKernel (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (θ : pol.Param)
    (z z' : (∀ i, S i) × (∀ i, A i)) : ℝ :=
  M.globalP z.1 z.2 z'.1 * pol.joint θ z'.1 z'.2

/-- The law of `z(0)`: `s(0) ∼ π₀`, `a(0) ∼ ζ^θ(· | s(0))`. -/
noncomputable def initLaw (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (θ : pol.Param)
    (z : (∀ i, S i) × (∀ i, A i)) : ℝ :=
  M.π₀ z.1 * pol.joint θ z.1 z.2

/-- The `t`-step law of the state-action chain under `θ` started at `z₀`. -/
noncomputable def chainLaw (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (θ : pol.Param)
    (z₀ : (∀ i, S i) × (∀ i, A i)) : ℕ → ((∀ i, S i) × (∀ i, A i)) → ℝ
  | 0 => fun z => if z = z₀ then 1 else 0
  | t + 1 => fun z' => ∑ z, chainLaw M pol θ z₀ t z * chainKernel M pol θ z z'

/-- The local state-action space `Z_{N_i^κ} = S_{N_i^κ} × A_{N_i^κ}` of the κ-hop neighbourhood. -/
abbrev LocSA (G : SimpleGraph (Fin n)) (κ : ℕ) (i : Fin n) (S A : Fin n → Type*) : Type _ :=
  (∀ j : nbhd G κ i, S j) × (∀ j : nbhd G κ i, A j)

/-- The restriction `z ↦ z_{N_i^κ} = (s_{N_i^κ}, a_{N_i^κ})`. -/
def restrictSA (G : SimpleGraph (Fin n)) (κ : ℕ) (i : Fin n) (z : (∀ i, S i) × (∀ i, A i)) :
    LocSA G κ i S A :=
  (fun j => z.1 j, fun j => z.2 j)

/-- Definition 1 (p. 8), the `(c, ρ)`-exponential decay property at hop count `κ`: for every
localized policy `θ`, every agent `i`, and all `z, z'` that agree on `N_i^κ`,
`|Q_i^θ(z) − Q_i^θ(z')| ≤ c ρ^{κ+1}`. -/
def ExpDecay (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (c ρ : ℝ) (κ : ℕ) : Prop :=
  ∀ (θ : pol.Param) (i : Fin n) (z z' : (∀ i, S i) × (∀ i, A i)),
    restrictSA M.G κ i z = restrictSA M.G κ i z' →
      |Qi M pol θ i z.1 z.2 - Qi M pol θ i z'.1 z'.2| ≤ c * ρ ^ (κ + 1)

/-- A truncated Q-function in the form (9)–(10), p. 9: there are nonnegative weights `w(·; x)`
on the global pairs `z` restricting to `x` (equivalently on `z_{N_{−i}^κ}`), summing to one for
every `x = z_{N_i^κ}`, with `Q̂_i(x) = Σ_{z : z_{N_i^κ} = x} w(z; x) Q_i^θ(z)`. -/
def IsTruncatedQ (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (θ : pol.Param) (κ : ℕ)
    (i : Fin n) (Qh : LocSA M.G κ i S A → ℝ) : Prop :=
  ∃ w : LocSA M.G κ i S A → ((∀ i, S i) × (∀ i, A i)) → ℝ,
    (∀ x z, 0 ≤ w x z) ∧
    (∀ x, ∑ z ∈ Finset.univ.filter (fun z => restrictSA M.G κ i z = x), w x z = 1) ∧
    ∀ x, Qh x = ∑ z ∈ Finset.univ.filter (fun z => restrictSA M.G κ i z = x),
      w x z * Qi M pol θ i z.1 z.2

end ScalableMARL



-- Prove2me | Definitions.Def_DeepBisimulationControl_Basic
-- name    : DeepBisimulationControl_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T07:02:16.158674+00:00
-- url     : https://prove2.me/theorems/851ea3b3-0f40-4d17-b0a2-e814acca0778
-- title:
--   Finite MDPs, bisimulation metrics, aggregation and causal ancestors (Deep Bisimulation for Control)
-- statement:
--   Objects of Sections 3-5 and Appendix A of Zhang, McAllister, Calandra, Gal and Levine (2021), on finite Markov decision processes.
--
--   1. **MDP.** A finite state space $\mathcal S$, a finite nonempty action space $\mathcal A$, transition probabilities $\mathcal P(s'\mid s,a)\ge0$ with $\sum_{s'}\mathcal P(s'\mid s,a)=1$, rewards $\mathcal R(s,a)\in\mathbb R$ and a discount factor $\gamma\in[0,1)$.
--   2. **Policies and values.** A policy $\pi(a\mid s)$ is a probability distribution on actions for each state; a deterministic policy $\sigma:\mathcal S\to\mathcal A$ plays $\sigma(s)$ with probability one. With $r^\pi_s=\sum_a\pi(a\mid s)\mathcal R(s,a)$ and $\mathcal P^\pi_s(s')=\sum_a\pi(a\mid s)\mathcal P(s'\mid s,a)$, the value of $\pi$ is $V^\pi=\sum_{n\ge0}\gamma^n(\mathcal P^\pi)^n r^\pi$, the optimal value is $V^*(s)=\sup_\pi V^\pi(s)$, and $\pi$ is optimal if $V^\pi=V^*$. The action value is $Q^\pi(s,a)=\mathcal R(s,a)+\gamma\sum_{s'}\mathcal P(s'\mid s,a)V^\pi(s')$.
--   3. **Policy iteration.** A sequence of deterministic policies $\sigma_0,\sigma_1,\dots$ with $\sigma_{k+1}(s)\in\arg\max_aQ^{\sigma_k}(s,a)$, keeping $\sigma_{k+1}(s)=\sigma_k(s)$ whenever $\sigma_k(s)$ is a maximiser.
--   4. **Wasserstein distance.** For distributions $\mu,\nu$ on $\mathcal S$ and a cost $d$, $W_1(\mu,\nu;d)=\inf_{\gamma'\in\Gamma(\mu,\nu)}\sum_{x,y}\gamma'(x,y)d(x,y)$, the infimum over couplings. A pseudometric is a nonnegative symmetric function with $d(s,s)=0$ satisfying the triangle inequality.
--   5. **Bisimulation metric (Definition 2).** For $c\in[0,1)$, $F(d)(s_i,s_j)=\max_a(1-c)|\mathcal R(s_i,a)-\mathcal R(s_j,a)|+c\,W_1(\mathcal P(\cdot\mid s_i,a),\mathcal P(\cdot\mid s_j,a);d)$, and the bisimulation metric is $\tilde d=\sup_nF^n(0)$.
--   6. **On-policy metric (Theorem 1).** $F(d,\pi)(s_i,s_j)=(1-c)|r^\pi_{s_i}-r^\pi_{s_j}|+c\,W_1(\mathcal P^\pi_{s_i},\mathcal P^\pi_{s_j};d)$ and the $\pi$-bisimulation metric is $\sup_nF(\cdot,\pi)^n(0)$. Along policy iteration the metric iterates are $d_0=0$, $d_{n+1}=F(d_n,\sigma_n)$.
--   7. **Aggregation (Theorem 2).** A map $\phi:\mathcal S\to C$ onto a finite set of clusters defines the aggregated MDP with averaged transitions $\bar{\mathcal P}(k'\mid k,a)=\frac1{|k|}\sum_{s\in k}\sum_{s'\in k'}\mathcal P(s'\mid s,a)$ and averaged rewards $\bar{\mathcal R}(k,a)=\frac1{|k|}\sum_{s\in k}\mathcal R(s,a)$. The average in-cluster distance is $g(s,d)=\frac1{|\phi(s)|}\sum_{s'\in\phi(s)}d(s,s')$. The aggregation is an $\varepsilon$-aggregation for $d$ if every cluster lies within distance $\varepsilon$ of some state.
--   8. **Representations.** $\|x-y\|_1=\sum_i|x_i-y_i|$ on $\mathbb R^m$; the learning error of an encoder $\psi:\mathcal S\to\mathbb R^m$ is $\mathcal L=\sup_{s_i,s_j}\big|\|\psi(s_i)-\psi(s_j)\|_1-\tilde d(s_i,s_j)\big|$.
--   9. **Factored MDPs and causal ancestors (Definition 3, Theorem 4).** The state is $s=(s^i)_{i\in I}$ with finite factors, and $\mathcal P(s'\mid s,a)=\prod_iT_i(s'^i\mid s,a)$. The causal graph has an edge from each factor in $\mathrm{pa}(i)$ to factor $i$ and from each factor in $\mathrm{pa}(R)$ to the reward. $AN(R)$ is the set of factors with a directed path to the reward.
--
--   **Formalization Note** Policies are stationary Markov policies; in a finite discounted MDP the supremum over them equals the optimum over all policies. The metrics are defined as suprema of iterates from the zero function, as in Ferns, Panangaden and Precup (2004), Theorem 4.5, so that each is a definite function of the data; that they solve their fixed-point equations is part of the statements. Values of the aggregated MDP are only used for surjective $\phi$, so no cluster is empty.
-- source:
--   Zhang, McAllister, Calandra, Gal and Levine, Learning Invariant Representations for Reinforcement Learning without Reconstruction, arXiv:2006.10742v2 (ICLR 2021), Section 3 (MDP, Definition 2, eq. (3)), Section 4 (l1 representation distance), Section 5 (Theorem 1 eq. (5), Theorem 2, learning error, Definition 3), Appendix A (proofs of Theorems 1, 2, 4); aggregated MDP from Ferns, Panangaden and Precup, UAI 2004, Section 5

import Mathlib

/-!
Zhang, McAllister, Calandra, Gal and Levine, *Learning Invariant Representations for Reinforcement
Learning without Reconstruction*, arXiv:2006.10742v2 (ICLR 2021): finite Markov decision processes,
policies and value functions (Section 3), the 1-Wasserstein distance and the bisimulation metric
(Section 3, Definition 2), the on-policy bisimulation operator and policy iteration (Section 5,
Theorem 1, Appendix A), the aggregated MDP of Theorem 2 (following Ferns, Panangaden and Precup,
UAI 2004, Section 5), the learning error of Section 5, and factored MDPs with causal ancestors
(Section 5, Definition 3, Theorem 4 and its proof in Appendix A).
-/

open Finset

noncomputable section

namespace DeepBisimulationControl

section MDP

variable {S A : Type*} [Fintype S] [Fintype A]

/-- Section 3: `P s a` is a probability distribution `P(· | s, a)` on the finite state space. -/
def IsKernel (P : S → A → S → ℝ) : Prop :=
  (∀ s a s', 0 ≤ P s a s') ∧ ∀ s a, ∑ s', P s a s' = 1

/-- Section 3: a (stationary, stochastic) policy `a ∼ π(s)`: `pi s` is a probability
distribution on actions. -/
def IsPolicy (pi : S → A → ℝ) : Prop :=
  (∀ s a, 0 ≤ pi s a) ∧ ∀ s, ∑ a, pi s a = 1

/-- The deterministic policy that plays `sigma s` in state `s` (Appendix A, proof of Theorem 1:
the policies `π_k(s) = argmax_a …` of policy iteration). -/
def detPolicy [DecidableEq A] (sigma : S → A) : S → A → ℝ :=
  fun s a => if a = sigma s then 1 else 0

/-- Section 5, Theorem 1: the on-policy reward `r^π_s = ∑_a π(a|s) R(s,a)`. -/
def policyReward (R : S → A → ℝ) (pi : S → A → ℝ) (s : S) : ℝ :=
  ∑ a, pi s a * R s a

/-- Section 5, Theorem 1: the on-policy transition distribution
`P^π_s(s') = ∑_a π(a|s) P(s'|s,a)`. -/
def policyKernel (P : S → A → S → ℝ) (pi : S → A → ℝ) (s s' : S) : ℝ :=
  ∑ a, pi s a * P s a s'

/-- Section 3: the value of policy `π`, the expected discounted return
`V^π(s) = E[∑_t γ^t R(s_t, a_t) | s_0 = s] = ∑_n γ^n ((P^π)^n r^π)(s)`. -/
def policyValue [DecidableEq S] (P : S → A → S → ℝ) (R : S → A → ℝ) (gamma : ℝ)
    (pi : S → A → ℝ) (s : S) : ℝ :=
  ∑' n : ℕ, gamma ^ n * (((Matrix.of (policyKernel P pi)) ^ n).mulVec (policyReward R pi)) s

/-- Section 3: the optimal value function `V*(s) = max_π E[∑_t γ^t R(s_t, a_t)]`, the supremum
of `V^π(s)` over stationary stochastic policies. -/
def optValue [DecidableEq S] (P : S → A → S → ℝ) (R : S → A → ℝ) (gamma : ℝ) (s : S) : ℝ :=
  ⨆ pi : {pi : S → A → ℝ // IsPolicy pi}, policyValue P R gamma pi.1 s

/-- Section 5, Theorems 1 and 5: `π*` is an optimal policy, `V^{π*} = V*`. -/
def IsOptimalPolicy [DecidableEq S] (P : S → A → S → ℝ) (R : S → A → ℝ) (gamma : ℝ)
    (pi : S → A → ℝ) : Prop :=
  IsPolicy pi ∧ ∀ s, policyValue P R gamma pi s = optValue P R gamma s

/-- Appendix A, proof of Theorem 1: the action value
`Q^π(s,a) = R(s,a) + γ ∑_{s'} P(s'|s,a) V^π(s')` maximised by policy iteration. -/
def qValue [DecidableEq S] (P : S → A → S → ℝ) (R : S → A → ℝ) (gamma : ℝ)
    (pi : S → A → ℝ) (s : S) (a : A) : ℝ :=
  R s a + gamma * ∑ s', P s a s' * policyValue P R gamma pi s'

/-- Appendix A, proof of Theorem 1, eqs. (10)-(11): `σ_0, σ_1, …` is a run of policy iteration,
`σ_{k+1}(s) ∈ argmax_a Q^{σ_k}(s,a)`, with the standard tie-breaking rule that
`σ_{k+1}(s) = σ_k(s)` whenever `σ_k(s)` is itself a maximiser. -/
def IsPolicyIteration [DecidableEq S] [DecidableEq A] (P : S → A → S → ℝ) (R : S → A → ℝ)
    (gamma : ℝ) (sigma : ℕ → S → A) : Prop :=
  ∀ k s,
    (∀ a, qValue P R gamma (detPolicy (sigma k)) s a ≤
      qValue P R gamma (detPolicy (sigma k)) s (sigma (k + 1) s)) ∧
    ((∀ a, qValue P R gamma (detPolicy (sigma k)) s a ≤
      qValue P R gamma (detPolicy (sigma k)) s (sigma k s)) → sigma (k + 1) s = sigma k s)

/-- Section 3, footnote 1: `d` is a pseudometric on the states (distinct states may be at
distance `0`). -/
def IsPseudometric (d : S → S → ℝ) : Prop :=
  (∀ s, d s s = 0) ∧ (∀ s t, 0 ≤ d s t) ∧ (∀ s t, d s t = d t s) ∧
    ∀ s t u, d s u ≤ d s t + d t u

/-- Section 3: `g` is a coupling of the distributions `mu` and `nu` on the states,
`g ∈ Γ(mu, nu)`. -/
def IsCoupling (mu nu : S → ℝ) (g : S → S → ℝ) : Prop :=
  (∀ x y, 0 ≤ g x y) ∧ (∀ x, ∑ y, g x y = mu x) ∧ ∀ y, ∑ x, g x y = nu y

/-- Section 3: the 1-Wasserstein distance with ground cost `d`,
`W_1(mu, nu; d) = inf_{g ∈ Γ(mu, nu)} ∑_{x,y} g(x,y) d(x,y)`. -/
def wasserstein1 (d : S → S → ℝ) (mu nu : S → ℝ) : ℝ :=
  sInf ((fun g : S → S → ℝ => ∑ x, ∑ y, g x y * d x y) '' {g | IsCoupling mu nu g})

/-- Section 3, Definition 2, eq. (3): the bisimulation operator
`F(d)(s_i,s_j) = max_a (1-c)|R(s_i,a) - R(s_j,a)| + c W_1(P(·|s_i,a), P(·|s_j,a); d)`. -/
def bisimOperator (P : S → A → S → ℝ) (R : S → A → ℝ) (c : ℝ) (d : S → S → ℝ) :
    S → S → ℝ :=
  fun s t => ⨆ a, (1 - c) * |R s a - R t a| + c * wasserstein1 d (P s a) (P t a)

/-- Section 3, Definition 2 (from Ferns et al.): the bisimulation metric, the solution of eq. (3),
constructed as in Ferns, Panangaden and Precup (2004), Theorem 4.5: `d̃ = sup_n F^n(0)`. -/
def bisimMetric (P : S → A → S → ℝ) (R : S → A → ℝ) (c : ℝ) : S → S → ℝ :=
  fun s t => ⨆ n : ℕ, ((bisimOperator P R c)^[n] 0) s t

/-- Section 5, Theorem 1, eq. (5): the on-policy bisimulation operator
`F(d, π)(s_i,s_j) = (1-c)|r^π_{s_i} - r^π_{s_j}| + c W_1(P^π_{s_i}, P^π_{s_j}; d)`. -/
def piBisimOperator (P : S → A → S → ℝ) (R : S → A → ℝ) (c : ℝ) (pi : S → A → ℝ)
    (d : S → S → ℝ) : S → S → ℝ :=
  fun s t => (1 - c) * |policyReward R pi s - policyReward R pi t| +
    c * wasserstein1 d (policyKernel P pi s) (policyKernel P pi t)

/-- Section 5, Theorems 1 and 5: the `π`-bisimulation metric `sup_n F(·, π)^n(0)`, the iterates
of the on-policy operator started at the bottom element `⊥ = 0`. -/
def piBisimMetric (P : S → A → S → ℝ) (R : S → A → ℝ) (c : ℝ) (pi : S → A → ℝ) :
    S → S → ℝ :=
  fun s t => ⨆ n : ℕ, ((piBisimOperator P R c pi)^[n] 0) s t

/-- Section 5, Theorem 1 and Appendix A: the metric iterates run alongside policy iteration,
`d_0 = ⊥ = 0`, `d_{n+1} = F(d_n, σ_n)`. -/
def policyIterationMetric [DecidableEq A] (P : S → A → S → ℝ) (R : S → A → ℝ) (c : ℝ)
    (sigma : ℕ → S → A) : ℕ → S → S → ℝ
  | 0 => 0
  | n + 1 => piBisimOperator P R c (detPolicy (sigma n)) (policyIterationMetric P R c sigma n)

section Aggregation

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Section 5, Theorem 2 (aggregated MDP `M̄`, as in Ferns et al. 2004, Section 5): the members
`{s | φ(s) = k}` of cluster `k`. -/
def cluster (phi : S → C) (k : C) : Finset S :=
  univ.filter fun s => phi s = k

/-- Section 5, Theorem 2: transitions of the aggregated MDP, averaged over the cluster,
`P̄(k' | k, a) = (1/|k|) ∑_{s ∈ k} ∑_{s' ∈ k'} P(s'|s,a)`. -/
def aggKernel (P : S → A → S → ℝ) (phi : S → C) (k : C) (a : A) (k' : C) : ℝ :=
  (∑ s ∈ cluster phi k, ∑ s' ∈ cluster phi k', P s a s') / (cluster phi k).card

/-- Section 5, Theorem 2: rewards of the aggregated MDP, averaged over the cluster,
`R̄(k, a) = (1/|k|) ∑_{s ∈ k} R(s,a)`. -/
def aggReward (R : S → A → ℝ) (phi : S → C) (k : C) (a : A) : ℝ :=
  (∑ s ∈ cluster phi k, R s a) / (cluster phi k).card

/-- Appendix A, proof of Theorem 2: `g(s, d)`, the average `d`-distance from `s` to the states of
its own cluster. -/
def avgClusterDist (d : S → S → ℝ) (phi : S → C) (s : S) : ℝ :=
  (∑ s' ∈ cluster phi (phi s), d s s') / (cluster phi (phi s)).card

/-- Section 5, Theorem 2: every cluster of `φ` lies in an `ε`-neighborhood of some state for the
distance `d`. -/
def IsEpsAggregation (d : S → S → ℝ) (phi : S → C) (eps : ℝ) : Prop :=
  ∀ k, ∃ s0 : S, ∀ s, phi s = k → d s0 s ≤ eps

end Aggregation

/-- Section 4: the `ℓ_1` distance `‖x - y‖_1` between two representations in `ℝ^m`. -/
def l1Dist {m : ℕ} (x y : Fin m → ℝ) : ℝ :=
  ∑ i, |x i - y i|

/-- Section 5, after Theorem 2: the learning error of an encoder `ψ`,
`L = sup_{s_i, s_j} |‖ψ(s_i) - ψ(s_j)‖_1 - d̃(s_i, s_j)|`. -/
def learningError {m : ℕ} (d : S → S → ℝ) (psi : S → Fin m → ℝ) : ℝ :=
  ⨆ st : S × S, |l1Dist (psi st.1) (psi st.2) - d st.1 st.2|

end MDP

section Factored

variable {I A : Type*} [Fintype I] [DecidableEq I] {X : I → Type*} [∀ i, Fintype (X i)]

/-- Appendix A, proof of Theorem 4: the transition of a factored MDP with state space
`S = ∏_i S^i` and one-step causal dynamics,
`P(s' | s, a) = ∏_i T_i(s'^i | s, a)`. -/
def factoredKernel (T : ∀ i, (∀ j, X j) → A → X i → ℝ) (s : ∀ j, X j) (a : A)
    (s' : ∀ j, X j) : ℝ :=
  ∏ i, T i s a (s' i)

/-- Appendix A, proof of Theorem 4: `f` depends on the state only through the factors in `J`. -/
def DependsOnlyOn {β : Type*} (f : (∀ j, X j) → β) (J : Set I) : Prop :=
  ∀ s s' : ∀ j, X j, (∀ j ∈ J, s j = s' j) → f s = f s'

/-- Section 5, Definition 3: the causal ancestors `AN(R)` of the reward in the causal graph whose
edges go from each factor in `pa i` to factor `i` and from each factor in `paR` to the reward:
the factors with a directed path to the reward. -/
def causalAncestors (pa : I → Set I) (paR : Set I) : Set I :=
  {j | ∃ i ∈ paR, Relation.ReflTransGen (fun x y => x ∈ pa y) j i}

end Factored

end DeepBisimulationControl



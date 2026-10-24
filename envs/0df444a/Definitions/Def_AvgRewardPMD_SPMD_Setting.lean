-- Prove2me | Definitions.Def_AvgRewardPMD_SPMD_Setting
-- name    : AvgRewardPMD_SPMD_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:43:25.435985+00:00
-- url     : https://prove2.me/theorems/72e1549e-9e63-429c-9a28-7d849d3d68ac
-- title:
--   §2.1, §3.1, pp. 5–9 — average-reward MDP: mixing (Assumption 1), average cost (2.1), differential V̄^π, Q̄^π, KL, span, (2.2), SPMD step (3.6), Assumption 3
-- statement:
--   The objects of the average-reward MDP and of stochastic policy mirror descent (SPMD), following Li, Wu and Lan (§2.1, pp. 5–6; §3.1, pp. 8–9).
--
--   An **AMDP** $\mathcal M=(\mathcal S,\mathcal A,\mathsf P,c)$ has finite state and action spaces, a transition kernel $\mathsf P(s'\mid s,a)$ and a real cost $c(s,a)$. A randomized stationary **policy** maps each state $s$ to a distribution $\pi(\cdot\mid s)\in\Delta_{|\mathcal A|}$.
--
--   1. **Transition matrices.** $P_\pi(s,s')=\sum_{a}\pi(a\mid s)\mathsf P(s'\mid s,a)$ on states and $P^\pi((s,a),(s',a'))=\mathsf P(s'\mid s,a)\,\pi(a'\mid s')$ on state–action pairs.
--   2. **Mixing (Assumption 1).** There is a finite $t_{\mathrm{mix}}$ such that every feasible policy $\pi$ has a stationary distribution $\nu^\pi$ of $P_\pi$ and some $1\le t\le t_{\mathrm{mix}}$ with
--   $$\max_{q\in\Delta_{|\mathcal S|}}\big\|((P_\pi)^t)^\top q-\nu^\pi\big\|_1\le\tfrac12 .$$
--   3. **Average cost (2.1).** For a per-step cost $c$ (a regularized cost $c(s,a)+h^\pi(s)$ is passed as the cost),
--   $$\rho^\pi(s)=\lim_{T\to\infty}\frac1T\sum_{t=0}^{T-1}\mathbb E_\pi[c(s_t,a_t)\mid s_0=s],\qquad \mathbb E_\pi[c(s_t,a_t)\mid s_0=s]=(P_\pi^t c^\pi)(s),$$
--   where $c^\pi(s)=\sum_a c(s,a)\pi(a\mid s)$.
--   4. **Differential functions** (p. 6). $\bar V^\pi(s)=\sum_{t\ge0}\big(\mathbb E_\pi[c(s_t,a_t)\mid s_0=s]-\rho^\pi\big)$ and $\bar Q^\pi(s,a)=\sum_{t\ge0}\big(\mathbb E_\pi[c(s_t,a_t)\mid s_0=s,a_0=a]-\rho^\pi\big)$.
--   5. **KL divergence and span.** $D^p_q=\sum_a p(a)\log\frac{p(a)}{q(a)}$ and $\|x\|_{\mathrm{sp}}=\max_i x_i-\min_i x_i$.
--   6. **Regularizer (2.2).** $h^\pi(s)=h_s(\pi(\cdot\mid s))$ is convex on $\Delta_{|\mathcal A|}$ with modulus $\omega\ge0$: at every strictly positive $\pi'$ some subgradient $g$ satisfies $h^\pi(s)-[h^{\pi'}(s)+\langle g,\pi(\cdot\mid s)-\pi'(\cdot\mid s)\rangle]\ge\omega D^\pi_{\pi'}(s)$ for every $\pi$. $h$ is $L$-Lipschitz if $|h_s(p)-h_s(p')|\le L\|p-p'\|_1$.
--   7. **SPMD (Algorithm 1, (3.6)).** $\pi_0(a\mid s)=1/|\mathcal A|$ and $\pi_{k+1}(\cdot\mid s)$ minimizes $\lambda_k[\langle \bar{\mathcal Q}^{\pi_k,\zeta_k}(s,\cdot),p\rangle+h^p(s)]+D^p_{\pi_k}(s)$ over $p\in\Delta_{|\mathcal A|}$, for every sample outcome.
--   8. **Distance to a comparator** (Lemma 4). $D(\pi,\pi')=\mathbb E_{s\sim\nu}[D^{\pi'}_\pi(s)]$.
--   9. **Assumption 3** (for the first $n$ steps). With $\mathcal F_{k-1}$ the past of the run and $\mathbb E_{\zeta_k}$ the conditional expectation given it, $\tilde{\mathcal Q}^{\pi_k}=\mathbb E_{\zeta_k}[\bar{\mathcal Q}^{\pi_k,\zeta_k}]$ satisfies $\|\tilde{\mathcal Q}^{\pi_k}-\bar Q^{\pi_k}\|_{\mathrm{sp}}\le\varsigma$ (3.7) and $\mathbb E_{\zeta_k}\|\bar{\mathcal Q}^{\pi_k,\zeta_k}\|^2_{\mathrm{sp}}\le\kappa^2$ (3.9).
--
--   These are the objects every statement of the mission is about; the goal is Theorem 1's convergence bound for the iterates of item 7 under item 9.
--
--   **Formalization Note** The general objects are the published `IsTransitionKernel`, `IsPolicy`, `InducedTransition`, `InducedReward` and `MarkovMixing.IsStationary`. Expectations along the chain are matrix powers. $\rho$ is a `limUnder` of the Cesàro means (the limit exists under Assumption 1); $\bar V,\bar Q$ are `tsum`s of the series of expectations, which converge absolutely under Assumption 1. `kl` uses `Real.log`; it is the true KL whenever the second argument is strictly positive, which holds for every SPMD iterate, and (2.2) is required only at strictly positive points. `span` is `⨆ − ⨅` over a finite index set. Assumption 3 is stated on a probability space with a filtration `ℱ`, `ℱ k` playing $\mathcal F_{k-1}$: $\pi_k$ is `ℱ k`-measurable, every entry of the critic output is integrable, (3.7) and (3.9) hold almost surely for the conditional expectations given `ℱ k`, and $\|\bar{\mathcal Q}^{\pi_k,\zeta_k}\|^2_{\mathrm{sp}}$ is integrable. (3.8) is not part of the predicate: no statement of the mission uses it.
-- source:
--   Li, Wu, Lan, Stochastic first-order methods for average-reward Markov decision processes, arXiv:2205.05800v6, pp. 5–9, §2.1 (2.1)–(2.2), Assumption 1, p. 6 displays, Algorithm 1 (3.5)–(3.6), Assumption 3 (3.7), (3.9), Lemma 4 (definition of D)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedTransition
import Definitions.Def_FoundationsML_ReinforcementLearning_InducedReward
import Definitions.Def_mm_basic

namespace AvgRewardPMD.SPMD

open FoundationsML.ReinforcementLearning MeasureTheory Filter

noncomputable section

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- The state–action transition matrix `P^π((s,a),(s',a')) = P(s'|s,a) π(a'|s')` induced by a
policy `π` (Li–Wu–Lan, arXiv:2205.05800v6, §2.1, p. 5). -/
def saTransition (P : S → A → S → ℝ) (π : S → A → ℝ) : Matrix (S × A) (S × A) ℝ :=
  Matrix.of fun x y => P x.1 x.2 y.1 * π y.1 y.2

/-- The state transition matrix `P_π(s,s') = ∑_a π(a|s) P(s'|s,a)` induced by a policy `π`
(§2.1, p. 5), as a matrix. -/
def stateMatrix (P : S → A → S → ℝ) (π : S → A → ℝ) : Matrix S S ℝ :=
  Matrix.of (InducedTransition π P)

/-- Assumption 1 (mixing AMDP, pp. 5–6): there is a finite `t_mix` such that every feasible
policy `π` has a stationary distribution `ν^π` of `P_π` and some `t ∈ [1, t_mix]` with
`max_{q ∈ Δ_|S|} ‖((P_π)^t)ᵀ q − ν^π‖₁ ≤ 1/2`. -/
def IsMixing (P : S → A → S → ℝ) : Prop :=
  ∃ tmix : ℕ, ∀ π : S → A → ℝ, IsPolicy π →
    ∃ ν : S → ℝ, MarkovMixing.IsStationary (stateMatrix P π) ν ∧
      ∃ t : ℕ, 1 ≤ t ∧ t ≤ tmix ∧
        ∀ q ∈ stdSimplex ℝ S,
          ∑ s', |∑ s, q s * ((stateMatrix P π) ^ t) s s' - ν s'| ≤ 1 / 2

/-- The long-run average cost (2.1), p. 5, of policy `π` for the per-step cost `c` from start
state `s`: `ρ^π(s) = lim_{T→∞} (1/T) ∑_{t<T} E_π[c(s_t,a_t) | s_0 = s]`, where
`E_π[c(s_t,a_t) | s_0 = s] = (P_π^t c^π)(s)`. A regularized cost `c(s,a) + h^π(s)` is passed as
the cost argument. -/
def avgCost (P : S → A → S → ℝ) (π : S → A → ℝ) (c : S → A → ℝ) (s : S) : ℝ :=
  limUnder atTop (fun T : ℕ => (T : ℝ)⁻¹ *
    ∑ t ∈ Finset.range T, (((stateMatrix P π) ^ t).mulVec (InducedReward π c)) s)

/-- The basic differential value function (bias) `V̄^π(s) = ∑_{t≥0} (E_π[c(s_t,a_t) | s_0 = s] − ρ^π)`
(p. 6), read as the series of expectations. -/
def diffV (P : S → A → S → ℝ) (π : S → A → ℝ) (c : S → A → ℝ) (s : S) : ℝ :=
  ∑' t : ℕ, ((((stateMatrix P π) ^ t).mulVec (InducedReward π c)) s - avgCost P π c s)

/-- The basic differential Q-function
`Q̄^π(s,a) = ∑_{t≥0} (E_π[c(s_t,a_t) | s_0 = s, a_0 = a] − ρ^π)` (p. 6), read as the series of
expectations; `E_π[c(s_t,a_t) | s_0 = s, a_0 = a] = ((P^π)^t c)(s,a)`. -/
def diffQ (P : S → A → S → ℝ) (π : S → A → ℝ) (c : S → A → ℝ) (x : S × A) : ℝ :=
  ∑' t : ℕ, ((((saTransition P π) ^ t).mulVec (fun y => c y.1 y.2)) x - avgCost P π c x.1)

/-- The Kullback–Leibler divergence `D^p_q = ∑_a p(a) log (p(a)/q(a))` (p. 5). It is the true KL
divergence whenever `q` is strictly positive (`0 · log 0 = 0`). -/
def kl (p q : A → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

/-- The span semi-norm `‖x‖_sp = max_i x_i − min_i x_i` (p. 5) of a vector on a finite index set. -/
def span {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  (⨆ i, x i) - ⨅ i, x i

/-- The per-state regularizer `H : Δ_|A| → ℝ` is convex with KL modulus `ω ≥ 0` ((2.2), p. 5):
`H` is convex on the simplex, and at every strictly positive `p'` some subgradient `g` satisfies
`H(p) − [H(p') + ⟨g, p − p'⟩] ≥ ω D^p_{p'}` for all `p` in the simplex. -/
def IsKLStrongConvexOn (H : (A → ℝ) → ℝ) (ω : ℝ) : Prop :=
  0 ≤ ω ∧ ConvexOn ℝ (stdSimplex ℝ A) H ∧
    ∀ p' ∈ stdSimplex ℝ A, (∀ a, 0 < p' a) →
      ∃ g : A → ℝ, ∀ p ∈ stdSimplex ℝ A,
        ω * kl p p' ≤ H p - (H p' + ∑ a, g a * (p a - p' a))

/-- The regularizer `h^π(s) = h s (π(·|s))` satisfies (2.2) with modulus `ω` at every state. -/
def IsKLStrongConvex (h : S → (A → ℝ) → ℝ) (ω : ℝ) : Prop :=
  ∀ s, IsKLStrongConvexOn (h s) ω

/-- The regularizer is `L`-Lipschitz in the policy, with respect to the `ℓ₁` norm on `Δ_|A|`. -/
def IsL1Lipschitz (h : S → (A → ℝ) → ℝ) (L : ℝ) : Prop :=
  ∀ s, ∀ p ∈ stdSimplex ℝ A, ∀ p' ∈ stdSimplex ℝ A, |h s p - h s p'| ≤ L * ∑ a, |p a - p' a|

/-- Algorithm 1 (SPMD, p. 8) run on every sample point `ξ`: `π 0 ξ` is the uniform policy, and
`π (k+1) ξ s` is a minimizer over `Δ_|A|` of the prox step (3.6)
`λ_k [⟨Q̂_k(s,·), p⟩ + h^p(s)] + D^p_{π_k}(s)`, where `Q̂_k = Qhat k ξ` is the critic output (3.5). -/
def IsSPMDIterates {Ω : Type*} (h : S → (A → ℝ) → ℝ) (lam : ℕ → ℝ)
    (Qhat : ℕ → Ω → S × A → ℝ) (π : ℕ → Ω → S → A → ℝ) : Prop :=
  ∀ ξ : Ω, (∀ s a, π 0 ξ s a = 1 / (Fintype.card A : ℝ)) ∧
    ∀ k s, π (k + 1) ξ s ∈ stdSimplex ℝ A ∧
      ∀ p ∈ stdSimplex ℝ A,
        lam k * (∑ a, Qhat k ξ (s, a) * π (k + 1) ξ s a + h s (π (k + 1) ξ s))
            + kl (π (k + 1) ξ s) (π k ξ s)
          ≤ lam k * (∑ a, Qhat k ξ (s, a) * p a + h s p) + kl p (π k ξ s)

/-- The distance `D(π, π') = E_{s∼ν}[D^{π'}_π(s)] = ∑_s ν(s) KL(π'(·|s) ‖ π(·|s))` of Lemma 4, p. 10,
with respect to the weight vector `ν` (the stationary distribution `ν*` of the comparator). -/
def stationaryKL (ν : S → ℝ) (π π' : S → A → ℝ) : ℝ :=
  ∑ s, ν s * kl (π' s) (π s)

/-- Assumption 3 (p. 8) for the first `n` critic outputs `Qhat k` (`k < n`) and the iterates `π k`
(`k ≤ n`) on a probability space with filtration `ℱ`, where `ℱ k` is the paper's
`F_{k−1} = σ(ζ_0, …, ζ_{k−1})` and `E_{ζ_k}` is the conditional expectation given `ℱ k`.
`Qbar π'` is the exact basic differential Q-function of `π'`. The conjuncts are: `π_k` is
`ℱ k`-measurable; `Q̂_k` is integrable (so `Q̃^{π_k} = E_{ζ_k}[Q̂_k]` is defined);
(3.7) `‖Q̃^{π_k} − Q̄^{π_k}‖_sp ≤ ς`; and (3.9) `E_{ζ_k}[‖Q̂_k‖²_sp] ≤ κ²`, with `‖Q̂_k‖²_sp`
integrable. -/
def CriticAssumption {Ω : Type*} {m : MeasurableSpace Ω} (μ : Measure Ω) (ℱ : Filtration ℕ m)
    (Qbar : (S → A → ℝ) → S × A → ℝ) (Qhat : ℕ → Ω → S × A → ℝ) (π : ℕ → Ω → S → A → ℝ)
    (bias κ : ℝ) (n : ℕ) : Prop :=
  (∀ k ≤ n, ∀ s a, Measurable[ℱ k] (fun ξ => π k ξ s a)) ∧
  (∀ k < n, ∀ x, Integrable (fun ξ => Qhat k ξ x) μ) ∧
  (∀ k < n, ∀ᵐ ξ ∂μ, span (fun x => μ[fun ξ' => Qhat k ξ' x | ℱ k] ξ - Qbar (π k ξ) x) ≤ bias) ∧
  (∀ k < n, Integrable (fun ξ => span (Qhat k ξ) ^ 2) μ ∧
    ∀ᵐ ξ ∂μ, μ[fun ξ' => span (Qhat k ξ') ^ 2 | ℱ k] ξ ≤ κ ^ 2)

end

end AvgRewardPMD.SPMD



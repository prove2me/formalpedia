-- Prove2me | Definitions.Def_OfflineZeroSumMG_MarkovGame
-- name    : OfflineZeroSumMG_MarkovGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:26:17.930267+00:00
-- url     : https://prove2.me/theorems/64a63f84-0637-466c-8474-368386991a1f
-- title:
--   §2.1 — discounted zero-sum Markov game, stationary policies, values $V^{\mu,\nu}$, best responses, Nash equilibria, occupancy $d^{\mu,\nu}$
-- statement:
--   This module sets up the model of §2.1 (pp.4–5).
--
--   1. **The game.** A discounted two-player zero-sum Markov game $\mathrm{MG}=(\mathcal S,\mathcal A,\mathcal B,P,r,\gamma)$ has states $\mathcal S=\{1,\dots,S\}$, max-player actions $\mathcal A=\{1,\dots,A\}$, min-player actions $\mathcal B=\{1,\dots,B\}$, a transition kernel $P(s'\mid s,a,b)$ with every row in $\Delta(\mathcal S)$, and rewards $r(s,a,b)\in[0,1]$.
--   2. **Policies.** A stationary randomized policy of the max-player is a map $\mu:\mathcal S\to\Delta(\mathcal A)$, and likewise $\nu:\mathcal S\to\Delta(\mathcal B)$; $1_{f(s)}$ denotes the deterministic policy playing $f(s)$.
--   3. **Induced chain.** $r^{\mu,\nu}(s)=\mathbb E_{a\sim\mu(s),b\sim\nu(s)}[r(s,a,b)]$ and $P^{\mu,\nu}(s'\mid s)=\mathbb E_{a\sim\mu(s),b\sim\nu(s)}[P(s'\mid s,a,b)]$ (B.15a), (B.15c).
--   4. **Values.** $V^{\mu,\nu}(s)=\mathbb E\big[\sum_{t\ge0}\gamma^t r(s_t,a_t,b_t)\mid s_0=s\big]$, $Q^{\mu,\nu}(s,a,b)=r(s,a,b)+\gamma\sum_{s'}P(s'\mid s,a,b)V^{\mu,\nu}(s')$, and $V(\rho)=\sum_s\rho(s)V(s)$.
--   5. **Best responses.** $V^{\mu,\star}=\min_\nu V^{\mu,\nu}$, $V^{\star,\nu}=\max_\mu V^{\mu,\nu}$, $Q^{\mu,\star}=\min_\nu Q^{\mu,\nu}$, $Q^{\star,\nu}=\max_\mu Q^{\mu,\nu}$ (p.5, Appendix A).
--   6. **Nash equilibrium.** $(\mu^\star,\nu^\star)$ is a Nash equilibrium if $V^{\mu,\nu^\star}\le V^{\mu^\star,\nu^\star}\le V^{\mu^\star,\nu}$ for all policies $\mu,\nu$; its value is $V^\star=V^{\mu^\star,\nu^\star}$.
--   7. **Occupancy.** $d^{\mu,\nu}(s;\rho)=(1-\gamma)\sum_{t\ge0}\gamma^t\,\mathbb P(s_t=s\mid s_0\sim\rho)$ (2.1) and $d^{\mu,\nu}(s,a,b;\rho)=d^{\mu,\nu}(s;\rho)\mu(a\mid s)\nu(b\mid s)$ (2.2)–(2.3).
--
--   These are the objects in which the paper's guarantees are stated: the duality gap $V^{\star,\hat\nu}(\rho)-V^{\hat\mu,\star}(\rho)$ and the coverage assumption.
--
--   **Formalization Note** States and actions are `Fin S`, `Fin A`, `Fin B` (0-based). Policies are maps into `stdSimplex`. The value is the series $\sum_t\gamma^t((P^{\mu,\nu})^t r^{\mu,\nu})(s)$, because the law of $s_t$ is the $t$-th power of $P^{\mu,\nu}$; $Q^{\mu,\nu}$ is written by its first-step decomposition. Best responses are real `⨅`/`⨆` over all stationary randomized policies; for $0<A,B$, $0\le\gamma<1$ and $r\in[0,1]$ these families are nonempty and bounded in $[0,1/(1-\gamma)]$, so the extrema are the paper's attained min and max. The discount $\gamma$ is a parameter; each theorem states its range.
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), §2.1, p.4 (game, policies, $V^{\mu,\nu}$, $Q^{\mu,\nu}$, $V(\rho)$); (2.1)–(2.3), pp.4–5; Nash equilibrium and best responses, p.5; Appendix A, p.13; (B.14)–(B.15), pp.16–17

import Mathlib

open Matrix

namespace OfflineZeroSumMG

/-! # Discounted two-player zero-sum Markov games with stationary randomized policies

Yan, Li, Chen & Fan, *Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games*,
arXiv:2206.04044v2, §2.1, pp.4–5, (2.1)–(2.3); Appendix A, p.13.

The game `MG = (S, A, B, P, r, γ)`, stationary randomized policies `μ : S → Δ(A)`,
`ν : S → Δ(B)`, the value and Q-functions `V^{μ,ν}`, `Q^{μ,ν}`, the best-response values
`V^{μ,⋆}`, `V^{⋆,ν}`, `Q^{μ,⋆}`, `Q^{⋆,ν}`, Nash equilibria, and the discounted occupancy
distributions `d^{μ,ν}(·; ρ)`.

**Formalization Note.** States and actions are `Fin S`, `Fin A`, `Fin B` (0-based; the paper's
`{1, …, S}`); every theorem assumes `0 < S`, `0 < A`, `0 < B`. The transition kernel is
`P s a b s' = P(s' | s, a, b)` and the reward is `r s a b`; `IsGame P r` says every row
`P s a b` is a probability vector and `0 ≤ r ≤ 1`. The discount `γ` is a parameter of each
definition and its range is a hypothesis of each theorem. -/

/-- A transition kernel `P : S × A × B → Δ(S)`, written `P s a b s' = P(s' | s, a, b)`. -/
abbrev Kernel (S A B : ℕ) := Fin S → Fin A → Fin B → Fin S → ℝ

/-- A reward function `r : S × A × B → ℝ`. -/
abbrev Reward (S A B : ℕ) := Fin S → Fin A → Fin B → ℝ

/-- The standing assumptions on the game of §2.1 (arXiv:2206.04044v2, p.4): every row
`P(· | s, a, b)` lies in the probability simplex `Δ(S)` and `r(s, a, b) ∈ [0, 1]`. -/
def IsGame {S A B : ℕ} (P : Kernel S A B) (r : Reward S A B) : Prop :=
  (∀ s a b, P s a b ∈ stdSimplex ℝ (Fin S)) ∧ (∀ s a b, 0 ≤ r s a b ∧ r s a b ≤ 1)

/-- A stationary randomized policy `S → Δ(K)` (arXiv:2206.04044v2, p.4, "(possibly random)
stationary policies"): for every state a point of the probability simplex on `Fin K`.
`μ s a = μ(a | s)`. -/
abbrev Policy (S K : ℕ) := Fin S → stdSimplex ℝ (Fin K)

/-- The deterministic policy that plays the action `f s` with probability one in state `s`,
i.e. `s ↦ 1_{f(s)}` (arXiv:2206.04044v2, (B.14), p.16, "a probability vector that is nonzero
only in `b_s`"). -/
def purePolicy {S K : ℕ} (f : Fin S → Fin K) : Policy S K :=
  fun s => ⟨fun k => if k = f s then 1 else 0, by
    refine ⟨fun k => by dsimp only; split_ifs <;> norm_num, ?_⟩
    simp⟩

/-- The one-step expected reward under the product policy `μ × ν`,
`r^{μ,ν}(s) = E_{a∼μ(s), b∼ν(s)}[r(s, a, b)]` (arXiv:2206.04044v2, (B.15a), p.17). -/
def rPol {S A B : ℕ} (r : Reward S A B) (μ : Policy S A) (ν : Policy S B) : Fin S → ℝ :=
  fun s => ∑ a, ∑ b, (μ s : Fin A → ℝ) a * (ν s : Fin B → ℝ) b * r s a b

/-- The state transition matrix under `μ × ν`,
`P^{μ,ν}(s' | s) = E_{a∼μ(s), b∼ν(s)}[P(s' | s, a, b)]` (arXiv:2206.04044v2, (B.15c), p.17). -/
def PPol {S A B : ℕ} (P : Kernel S A B) (μ : Policy S A) (ν : Policy S B) :
    Matrix (Fin S) (Fin S) ℝ :=
  fun s s' => ∑ a, ∑ b, (μ s : Fin A → ℝ) a * (ν s : Fin B → ℝ) b * P s a b s'

/-- The value function `V^{μ,ν}(s) = E[∑_{t≥0} γ^t r(s_t, a_t, b_t) | s_0 = s; μ, ν]`
(arXiv:2206.04044v2, p.4).

**Formalization Note.** Under `μ × ν` the states form a Markov chain with transition matrix
`P^{μ,ν}`, so `E[r(s_t, a_t, b_t) | s_0 = s] = ((P^{μ,ν})^t r^{μ,ν})(s)` and the value is the
series `∑' t, γ^t ((P^{μ,ν})^t r^{μ,ν})(s)`; for `0 ≤ γ < 1` and `r ∈ [0, 1]` its terms are
nonnegative and bounded by `γ^t`, so the series converges. -/
noncomputable def V {S A B : ℕ} (P : Kernel S A B) (r : Reward S A B) (γ : ℝ)
    (μ : Policy S A) (ν : Policy S B) : Fin S → ℝ :=
  fun s => ∑' t : ℕ, γ ^ t * (((PPol P μ ν) ^ t) *ᵥ rPol r μ ν) s

/-- The Q-function `Q^{μ,ν}(s, a, b) = E[∑_{t≥0} γ^t r(s_t, a_t, b_t) | s_0 = s, a_0 = a,
b_0 = b; μ, ν]` (arXiv:2206.04044v2, p.4).

**Formalization Note.** Written by its first-step decomposition
`r(s, a, b) + γ ∑_{s'} P(s' | s, a, b) V^{μ,ν}(s')`: after the first transition the play
continues under `μ × ν` from `s_1 ∼ P(· | s, a, b)`. -/
noncomputable def Qfun {S A B : ℕ} (P : Kernel S A B) (r : Reward S A B) (γ : ℝ)
    (μ : Policy S A) (ν : Policy S B) : Fin S → Fin A → Fin B → ℝ :=
  fun s a b => r s a b + γ * ∑ s', P s a b s' * V P r γ μ ν s'

/-- The value at an initial distribution, `V(ρ) = E_{s∼ρ}[V(s)] = ∑_s ρ(s) V(s)`
(arXiv:2206.04044v2, p.4; `ρ⊤V`, p.18). -/
def atDist {S : ℕ} (ρ : Fin S → ℝ) (W : Fin S → ℝ) : ℝ := ∑ s, ρ s * W s

/-- The min-player's best-response value `V^{μ,⋆}(s) = min_ν V^{μ,ν}(s)`
(arXiv:2206.04044v2, p.5; Appendix A, p.13), the minimum over stationary randomized `ν`.

**Formalization Note.** The real infimum over all policies `ν : Policy S B`; for `0 < B`,
`0 ≤ γ < 1` and an `IsGame` instance the family is nonempty and bounded (values lie in
`[0, 1/(1−γ)]`), and the minimum is attained (Appendix A). -/
noncomputable def VminBR {S A B : ℕ} (P : Kernel S A B) (r : Reward S A B) (γ : ℝ)
    (μ : Policy S A) : Fin S → ℝ :=
  fun s => ⨅ ν : Policy S B, V P r γ μ ν s

/-- The max-player's best-response value `V^{⋆,ν}(s) = max_μ V^{μ,ν}(s)`
(arXiv:2206.04044v2, p.5; Appendix A, p.13), the real supremum over stationary randomized `μ`. -/
noncomputable def VmaxBR {S A B : ℕ} (P : Kernel S A B) (r : Reward S A B) (γ : ℝ)
    (ν : Policy S B) : Fin S → ℝ :=
  fun s => ⨆ μ : Policy S A, V P r γ μ ν s

/-- `Q^{μ,⋆}(s, a, b) = min_ν Q^{μ,ν}(s, a, b)` (arXiv:2206.04044v2, Appendix A, p.13). -/
noncomputable def QminBR {S A B : ℕ} (P : Kernel S A B) (r : Reward S A B) (γ : ℝ)
    (μ : Policy S A) : Fin S → Fin A → Fin B → ℝ :=
  fun s a b => ⨅ ν : Policy S B, Qfun P r γ μ ν s a b

/-- `Q^{⋆,ν}(s, a, b) = max_μ Q^{μ,ν}(s, a, b)` (arXiv:2206.04044v2, Appendix A, p.13). -/
noncomputable def QmaxBR {S A B : ℕ} (P : Kernel S A B) (r : Reward S A B) (γ : ℝ)
    (ν : Policy S B) : Fin S → Fin A → Fin B → ℝ :=
  fun s a b => ⨆ μ : Policy S A, Qfun P r γ μ ν s a b

/-- `(μ⋆, ν⋆)` is a Nash equilibrium (arXiv:2206.04044v2, p.5): for all stationary
policies `μ`, `ν` and every state, `V^{μ,ν⋆} ≤ V^{μ⋆,ν⋆} ≤ V^{μ⋆,ν}`. Its value
`V⋆ = V^{μ⋆,ν⋆}` is `V P r γ μ⋆ ν⋆`. -/
def IsNash {S A B : ℕ} (P : Kernel S A B) (r : Reward S A B) (γ : ℝ)
    (μs : Policy S A) (νs : Policy S B) : Prop :=
  ∀ (μ : Policy S A) (ν : Policy S B) (s : Fin S),
    V P r γ μ νs s ≤ V P r γ μs νs s ∧ V P r γ μs νs s ≤ V P r γ μs ν s

/-- The discounted state occupancy distribution
`d^{μ,ν}(s; ρ) = (1 − γ) ∑_{t≥0} γ^t P(s_t = s | s_0 ∼ ρ; μ, ν)` (arXiv:2206.04044v2, (2.1),
p.4).

**Formalization Note.** The law of `s_t` under `s_0 ∼ ρ` is the row vector `ρ⊤(P^{μ,ν})^t`. -/
noncomputable def occState {S A B : ℕ} (P : Kernel S A B) (γ : ℝ) (ρ : Fin S → ℝ)
    (μ : Policy S A) (ν : Policy S B) : Fin S → ℝ :=
  fun s => (1 - γ) * ∑' t : ℕ, γ ^ t * (ρ ᵥ* ((PPol P μ ν) ^ t)) s

/-- The discounted state-action occupancy distribution `d^{μ,ν}(s, a, b; ρ)` of (2.2)
(arXiv:2206.04044v2, p.4), written by (2.3) (p.5) as `d^{μ,ν}(s; ρ) μ(a | s) ν(b | s)`.

**Formalization Note.** (2.2) is the discounted sum of `P(s_t = s, a_t = a, b_t = b)`, and
under a stationary product policy `P(s_t = s, a_t = a, b_t = b) = P(s_t = s) μ(a|s) ν(b|s)`,
which is (2.3). -/
noncomputable def occ {S A B : ℕ} (P : Kernel S A B) (γ : ℝ) (ρ : Fin S → ℝ)
    (μ : Policy S A) (ν : Policy S B) : Fin S → Fin A → Fin B → ℝ :=
  fun s a b => occState P γ ρ μ ν s * (μ s : Fin A → ℝ) a * (ν s : Fin B → ℝ) b

end OfflineZeroSumMG



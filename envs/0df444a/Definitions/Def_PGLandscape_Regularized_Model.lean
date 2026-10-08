-- Prove2me | Definitions.Def_PGLandscape_Regularized_Model
-- name    : PGLandscape_Regularized_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T05:26:49.644896+00:00
-- url     : https://prove2.me/theorems/186980dc-1542-43e8-b2a8-33f33ecae2bc
-- title:
--   Example 4, p. 19 — the KL-regularized finite MDP: D_KL(U‖a), g_λ (16), ℓ_λ and ℓ_0 (1), η_π (2), cost-optimal and barrier-greedy (36) policies, c of Lemma 10
-- statement:
--   This module sets up the regularized finite Markov decision process of Example 4 of Bhandari and Russo.
--
--   The state space $\mathcal S$ is a finite set and the action space is the probability simplex $\Delta_{k-1}$ over a finite set of $k$ deterministic actions $e_1,\dots,e_k$. A (stationary) policy $\pi$ assigns to each state $s$ a probability vector $\pi(s)=(\pi(1|s),\dots,\pi(k|s))\in\Delta_{k-1}$. Transitions are linear in the action, $P(s'|s,a)=\sum_{i=1}^k P(s'|s,e_i)\,a_i$, and each state carries a nonnegative cost vector $g_s\in\mathbb R^k_+$. For $\lambda\ge 0$ the regularized per-period cost is
--
--   $$
--   g_\lambda(s,a)=g_s^\top a+\lambda\,D_{\mathrm{KL}}(U\|a),\qquad D_{\mathrm{KL}}(U\|a)=\sum_{i=1}^k\frac1k\log\frac{1/k}{a_i},
--   $$
--
--   where $U$ is the uniform distribution; $D_{\mathrm{KL}}(U\|a)=+\infty$ unless $\min_i a_i>0$.
--
--   The module defines:
--   1. the divergence $D_{\mathrm{KL}}(U\|a)\in[0,\infty]$ and the cost $g_\lambda(s,a)\in[0,\infty]$;
--   2. the regularized discounted average cost $\ell_\lambda(\pi)=(1-\gamma)\sum_s\rho(s)\,\mathbb E^\pi_s\big[\sum_{t\ge0}\gamma^t g_\lambda(s_t,\pi(s_t))\big]\in[0,\infty]$;
--   3. the unregularized discounted average cost $\ell_0(\pi)=(1-\gamma)\sum_s\rho(s)J_{0,\pi}(s)$, where $J_{0,\pi}$ is the cost-to-go of the costs $g_s^\top a$;
--   4. the discounted state-occupancy distribution $\eta_\pi(s')=(1-\gamma)\sum_s\rho(s)\sum_{t\ge0}\gamma^t\Pr^\pi(s_t=s'\mid s_0=s)$;
--   5. cost-optimality of a policy $\pi_0$ for the unregularized problem ($J_{0,\pi_0}\le J_{0,\pi}$ pointwise for every policy $\pi$, so $J^*_0=J_{0,\pi_0}$ and $Q^*_0=Q_{0,\pi_0}$);
--   6. the standing setting: $P(\cdot|s,e_i)$ are probability vectors, $g_s\ge0$, $\gamma\in(0,1)$, $\rho$ a probability distribution;
--   7. the constant $c=2\max_{s,i}|g_{s,i}|/(1-\gamma)$;
--   8. barrier-greedy policies, the construction (36): $\pi_\lambda(s)$ minimizes $a\mapsto\sum_i Q^*_0(s,e_i)a_i+\lambda D_{\mathrm{KL}}(U\|a)$ over $\Delta_{k-1}$ at every state.
--
--   These objects state Lemma 10 (the impact of regularization) and the steps of its proof in Appendix E.2.
--
--   **Formalization Note** Actions $e_i$ are indexed by a finite type $I$ with $k=|I|$; policies, kernels, the cost-to-go $J_{0,\pi}$ (`PolicyValue` with the cost vector in the reward slot, a plain discounted sum) and $Q_{0,\pi}$ (`QFunction`) come from the published `FoundationsML.ReinforcementLearning` finite-MDP layer. Regularized quantities take values in $[0,\infty]$ so that $D_{\mathrm{KL}}=+\infty$ off the open simplex is represented exactly; with $\lambda=0$ the convention $0\cdot\infty=0$ makes $g_0(s,a)=g_s^\top a$. The constant $c$ needs $\mathcal S$ and the action set nonempty, as they are on the page.
-- source:
--   arXiv:1906.01786v3, Example 4, (16), p. 19; (1), (2), p. 6; Lemma 10, p. 20; (36), p. 44

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_PolicyValue
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction

namespace PGLandscape.Regularized

open FoundationsML.ReinforcementLearning
open scoped ENNReal

/-- `D_KL(U‖a) = Σ_{i=1}^k (1/k) log((1/k)/a_i)`, the Kullback–Leibler divergence of the uniform
distribution `U` on the `k = |I|` actions from `a` (Example 4, p. 19 of Bhandari and Russo,
arXiv:1906.01786v3). It is `+∞` unless every `a_i > 0`, so `dom(R) = {a : min_i a_i > 0}`. -/
noncomputable def klUniform {I : Type*} [Fintype I] (a : I → ℝ) : ℝ≥0∞ :=
  if ∀ i, 0 < a i then
    ENNReal.ofReal (∑ i, (1 / (Fintype.card I : ℝ)) * Real.log ((1 / (Fintype.card I : ℝ)) / a i))
  else ⊤

/-- The regularized per-period cost `g_λ(s, a) = g_s^⊤ a + λ D_KL(U‖a)` of (16), p. 19, with values
in `[0, ∞]` (`g_s ∈ ℝ^k_+`). -/
noncomputable def regCost {S I : Type*} [Fintype I] (gs : S → I → ℝ) (lam : ℝ) (a : I → ℝ)
    (s : S) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ i, a i * gs s i) + ENNReal.ofReal lam * klUniform a

/-- The regularized discounted average cost
`ℓ_λ(π) = (1 − γ) Σ_s ρ(s) E^π_s[Σ_{t≥0} γ^t g_λ(s_t, π(s_t))]` ((1), p. 6, for the MDP of Example 4),
an extended value in `[0, ∞]`. -/
noncomputable def regLoss {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (P : S → I → S → ℝ) (gs : S → I → ℝ) (γ : ℝ) (ρ : S → ℝ) (lam : ℝ) (π : S → I → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - γ) * ∑ s, ENNReal.ofReal (ρ s) * ∑' t : ℕ, ENNReal.ofReal (γ ^ t) *
    ∑ s', ENNReal.ofReal (OccupationDist π P s t s') * regCost gs lam (π s') s'

/-- The unregularized discounted average cost `ℓ_0(π) = (1 − γ) Σ_s ρ(s) J_{0,π}(s)`, (1), p. 6. -/
noncomputable def loss0 {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (P : S → I → S → ℝ) (gs : S → I → ℝ) (γ : ℝ) (ρ : S → ℝ) (π : S → I → ℝ) : ℝ :=
  (1 - γ) * ∑ s, ρ s * PolicyValue π P gs γ s

/-- The discounted state-occupancy distribution `η_π(s') = (1 − γ) Σ_s ρ(s) Σ_{t≥0} γ^t
Pr^π(s_t = s' | s_0 = s)`, (2), p. 6. -/
noncomputable def occFin {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (P : S → I → S → ℝ) (γ : ℝ) (ρ : S → ℝ) (π : S → I → ℝ) (s' : S) : ℝ :=
  (1 - γ) * ∑ s, ρ s * ∑' t : ℕ, γ ^ t * OccupationDist π P s t s'

/-- `π₀` is optimal for the unregularized (cost-minimizing) MDP: `π₀ ∈ Π` and
`J_{0,π₀}(s) ≤ J_{0,π}(s)` for every `π ∈ Π` and every state `s`, so `J*_0 = J_{0,π₀}`. -/
def IsCostOptimal {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (P : S → I → S → ℝ) (gs : S → I → ℝ) (γ : ℝ) (π₀ : S → I → ℝ) : Prop :=
  IsPolicy π₀ ∧ ∀ π : S → I → ℝ, IsPolicy π → ∀ s, PolicyValue π₀ P gs γ s ≤ PolicyValue π P gs γ s

/-- The standing setting of Examples 3–4 (pp. 18–19) and §2: `P(·|s, e_i)` are probability vectors,
`g_s ∈ ℝ^k_+`, `γ ∈ (0, 1)`, and `ρ` is a probability distribution on `S`. -/
def IsRegMDP {S I : Type*} [Fintype S] (P : S → I → S → ℝ) (gs : S → I → ℝ) (γ : ℝ)
    (ρ : S → ℝ) : Prop :=
  IsTransitionKernel P ∧ (∀ s i, 0 ≤ gs s i) ∧ 0 < γ ∧ γ < 1 ∧ (∀ s, 0 ≤ ρ s) ∧ ∑ s, ρ s = 1

/-- The constant `c = 2 (max_{s,i} |g_{s,i}|)/(1 − γ)` of Lemma 10, p. 20. -/
noncomputable def costConst {S I : Type*} [Fintype S] [Fintype I] [Nonempty S] [Nonempty I]
    (gs : S → I → ℝ) (γ : ℝ) : ℝ :=
  2 * (Finset.univ.sup' Finset.univ_nonempty (fun p : S × I => |gs p.1 p.2|)) / (1 - γ)

/-- `π'` is the barrier-greedy policy of (36), p. 44, with respect to `Q*_0 = Q_{0,π₀}`: `π' ∈ Π` and,
at every state `s`, `π'(s)` minimizes `a ↦ Σ_i Q*_0(s, e_i) a_i + λ D_KL(U‖a)` over the simplex
`∆_{k−1}` (objective values in `[0, ∞]`). -/
def IsBarrierGreedy {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (P : S → I → S → ℝ) (gs : S → I → ℝ) (γ lam : ℝ) (π₀ π' : S → I → ℝ) : Prop :=
  IsPolicy π' ∧ ∀ (s : S) (a : I → ℝ), (∀ i, 0 ≤ a i) → ∑ i, a i = 1 →
    ENNReal.ofReal (∑ i, QFunction π₀ P gs γ s i * π' s i) + ENNReal.ofReal lam * klUniform (π' s) ≤
      ENNReal.ofReal (∑ i, QFunction π₀ P gs γ s i * a i) + ENNReal.ofReal lam * klUniform a

end PGLandscape.Regularized



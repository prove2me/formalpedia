-- Prove2me | Definitions.Def_OfflineZeroSumMG_VILCBGame
-- name    : OfflineZeroSumMG_VILCBGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:27:52.693539+00:00
-- url     : https://prove2.me/theorems/37051406-a842-466b-8748-0e4e347630ab
-- title:
--   (3.3)–(3.5), Algorithm 1 — matrix-game value, penalty $\beta$, pessimistic operators $\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}$, VI-LCB-Game and its outputs
-- statement:
--   This module defines VI-LCB-Game (Algorithm 1, p.9).
--
--   1. **Matrix-game value (3.3).** For $Q:\mathcal S\times\mathcal A\times\mathcal B\to\mathbb R$, $V(s)=\max_{\mu_s\in\Delta(\mathcal A)}\min_{\nu_s\in\Delta(\mathcal B)}\mathbb E_{a\sim\mu_s,b\sim\nu_s}[Q(s,a,b)]$.
--   2. **Penalty (3.5).** With $L=\log(N/\delta)$,
--   $$\beta(s,a,b;V)=\min\Big\{\max\Big\{\sqrt{\tfrac{C_{\mathsf b}L}{N(s,a,b)}\mathrm{Var}_{\widehat P_{s,a,b}}(V)},\ \tfrac{2C_{\mathsf b}L}{(1-\gamma)N(s,a,b)}\Big\},\ \tfrac1{1-\gamma}\Big\}+\frac4N,$$
--   which equals $\frac1{1-\gamma}+\frac4N$ when $N(s,a,b)=0$.
--   3. **Pessimistic operators (3.4).** $\widehat{\mathcal T}^-_{\mathsf{pe}}(Q)(s,a,b)=\max\{\widehat r(s,a,b)+\gamma\widehat P_{s,a,b}V-\beta(s,a,b;V),0\}$ and $\widehat{\mathcal T}^+_{\mathsf{pe}}(Q)(s,a,b)=\min\{\widehat r(s,a,b)+\gamma\widehat P_{s,a,b}V+\beta(s,a,b;V),\frac1{1-\gamma}\}$, with $V$ from (3.3).
--   4. **Iterates.** $Q^-_{\mathsf{pe},0}=0$, $Q^+_{\mathsf{pe},0}=\frac1{1-\gamma}$, $Q^{\mp}_{\mathsf{pe},t}=\widehat{\mathcal T}^{\mp}_{\mathsf{pe}}(Q^{\mp}_{\mathsf{pe},t-1})$, $T=\lceil\log(N/(1-\gamma))/\log(1/\gamma)\rceil$, $Q^{\mp}_{\mathsf{pe}}=Q^{\mp}_{\mathsf{pe},T}$ and $V^{\mp}_{\mathsf{pe}}$ their values (3.3).
--   5. **Output.** $(\hat\mu,\hat\nu)$ is an output when, at every state $s$, $\hat\mu(s)$ is the max-player part of a solution of the matrix game $Q^-_{\mathsf{pe}}(s,\cdot,\cdot)$ and $\hat\nu(s)$ is the min-player part of a solution of $Q^+_{\mathsf{pe}}(s,\cdot,\cdot)$ (MatrixNash).
--   6. **Averaged penalty (B.15b).** $\beta^{\mu,\nu}(s)=\mathbb E_{a\sim\mu(s),b\sim\nu(s)}[\beta(s,a,b;V)]$.
--
--   **Formalization Note** The matrix-game value uses the published payoff `TheoryOfGames.Minimax.K` and its infimum `minK`; real `⨆`/`⨅` over the simplices are the attained max and min. Algorithm 1 sets $V^{\mp}_{\mathsf{pe},t}(s)$ to the expected payoff at the pair returned by MatrixNash; at every saddle point this payoff equals the value (3.3), so the iterates use the value and do not depend on which saddle point is returned. A solution of the minimax program is a saddle point (`IsMixedSaddlePoint`). The penalty's branch at $N(s,a,b)=0$ is the printed formula with $1/0=+\infty$, the value the paper uses on p.31, written explicitly instead of Lean's $x/0=0$.
-- source:
--   Yan, Li, Chen & Fan, Model-Based Reinforcement Learning for Offline Zero-Sum Markov Games, arXiv:2206.04044v2 (https://arxiv.org/abs/2206.04044v2), (3.3)–(3.6), p.7; (3.8)–(3.10), p.8; Algorithm 1, p.9; (B.15b), p.17

import Mathlib
import Definitions.Def_TheoryOfGames_Minimax_MixedStrategy
import Definitions.Def_OfflineZeroSumMG_OfflineData

namespace OfflineZeroSumMG

/-! # VI-LCB-Game: pessimistic value iteration for offline zero-sum Markov games

Yan, Li, Chen & Fan, arXiv:2206.04044v2, (3.3)–(3.5), p.7; (3.8)–(3.10), p.8; Algorithm 1, p.9.

All objects are computed from a dataset `D : Fin N → Sample S A B`, the reward `r`, the discount
`γ`, the algorithm's constant `C_b` (`Cb`) and the target failure probability `δ`.

**Formalization Note.**
1. The matrix-game value (3.3) is `gval M = max_{w ∈ Δ(A)} min_{z ∈ Δ(B)} w⊤Mz`, written with
   the published payoff `TheoryOfGames.Minimax.K` and `minK` (real `⨆`/`⨅` over the simplices,
   attained for `0 < A`, `0 < B`).
2. Algorithm 1 sets `V⁻_{pe,t}(s) = E_{a∼μ⁻_t(s), b∼ν⁻_t(s)}[Q⁻_{pe,t}(s, a, b)]` for the pair
   `(μ⁻_t(s), ν⁻_t(s))` returned by `MatrixNash`. At every saddle point this expected payoff equals
   `gval (Q⁻_{pe,t}(s, ·, ·))`, so the iterates use `gval`; they do not depend on which saddle
   point `MatrixNash` returns. The initial `V⁻_{pe,0} = gval 0 = 0` and
   `V⁺_{pe,0} = gval (1/(1−γ)) = 1/(1−γ)`.
3. The penalty (3.5) at `N(s, a, b) = 0` is the printed formula with `1/0 = +∞`:
   `min{+∞, 1/(1−γ)} + 4/N = 1/(1−γ) + 4/N` (the paper's value, p.31), written as an explicit
   branch, not with Lean's `x / 0 = 0`. -/

/-- The value (3.3) of the zero-sum matrix game with payoff matrix `M ∈ ℝ^{A×B}`
(arXiv:2206.04044v2, p.7): `max_{w ∈ Δ(A)} min_{z ∈ Δ(B)} E_{a∼w, b∼z}[M(a, b)]`. -/
noncomputable def gval {A B : ℕ} (M : Fin A → Fin B → ℝ) : ℝ :=
  ⨆ w : stdSimplex ℝ (Fin A), TheoryOfGames.Minimax.minK M w

/-- The value function associated with `Q` (3.3) (arXiv:2206.04044v2, p.7):
`V(s) = max_{μ_s} min_{ν_s} E_{a∼μ_s, b∼ν_s}[Q(s, a, b)]`. -/
noncomputable def Vof {S A B : ℕ} (Q : Fin S → Fin A → Fin B → ℝ) : Fin S → ℝ :=
  fun s => gval (Q s)

/-- The Bernstein-style penalty (3.5) (arXiv:2206.04044v2, p.7):
`β(s, a, b; V) = min{max{√(C_b log(N/δ) Var_{P̂_{s,a,b}}(V) / N(s, a, b)),
2 C_b log(N/δ) / ((1−γ) N(s, a, b))}, 1/(1−γ)} + 4/N`, and `1/(1−γ) + 4/N` when
`N(s, a, b) = 0`. Here `N` is the number of samples in `D`. -/
noncomputable def beta {S A B N : ℕ} (γ Cb δ : ℝ) (D : Fin N → Sample S A B)
    (s : Fin S) (a : Fin A) (b : Fin B) (W : Fin S → ℝ) : ℝ :=
  if cnt D s a b = 0 then 1 / (1 - γ) + 4 / (N : ℝ)
  else
    min (max (Real.sqrt (Cb * Real.log ((N : ℝ) / δ) / (cnt D s a b : ℝ) *
                varP (Phat D s a b) W))
             (2 * Cb * Real.log ((N : ℝ) / δ) / ((1 - γ) * (cnt D s a b : ℝ))))
        (1 / (1 - γ)) + 4 / (N : ℝ)

/-- The pessimistic Bellman operator of the max-player (3.4a) (arXiv:2206.04044v2, p.7):
`T̂⁻_pe(Q)(s, a, b) = max{r̂(s, a, b) + γ P̂_{s,a,b} V − β(s, a, b; V), 0}` with `V` from (3.3). -/
noncomputable def Tminus {S A B N : ℕ} (r : Reward S A B) (γ Cb δ : ℝ)
    (D : Fin N → Sample S A B) (Q : Fin S → Fin A → Fin B → ℝ) :
    Fin S → Fin A → Fin B → ℝ :=
  fun s a b =>
    max (rhat r D s a b + γ * ∑ s', Phat D s a b s' * Vof Q s' - beta γ Cb δ D s a b (Vof Q)) 0

/-- The pessimistic Bellman operator of the min-player (3.4b) (arXiv:2206.04044v2, p.7):
`T̂⁺_pe(Q)(s, a, b) = min{r̂(s, a, b) + γ P̂_{s,a,b} V + β(s, a, b; V), 1/(1−γ)}`. -/
noncomputable def Tplus {S A B N : ℕ} (r : Reward S A B) (γ Cb δ : ℝ)
    (D : Fin N → Sample S A B) (Q : Fin S → Fin A → Fin B → ℝ) :
    Fin S → Fin A → Fin B → ℝ :=
  fun s a b =>
    min (rhat r D s a b + γ * ∑ s', Phat D s a b s' * Vof Q s' + beta γ Cb δ D s a b (Vof Q))
      (1 / (1 - γ))

/-- The iterate `Q⁻_{pe,t} = (T̂⁻_pe)^t (Q⁻_{pe,0})` with `Q⁻_{pe,0} = 0` (Algorithm 1,
arXiv:2206.04044v2, p.9; (3.8), p.7). -/
noncomputable def QminusIter {S A B N : ℕ} (r : Reward S A B) (γ Cb δ : ℝ)
    (D : Fin N → Sample S A B) (t : ℕ) : Fin S → Fin A → Fin B → ℝ :=
  (Tminus r γ Cb δ D)^[t] (fun _ _ _ => 0)

/-- The iterate `Q⁺_{pe,t} = (T̂⁺_pe)^t (Q⁺_{pe,0})` with `Q⁺_{pe,0} = 1/(1−γ)` (Algorithm 1,
arXiv:2206.04044v2, p.9). -/
noncomputable def QplusIter {S A B N : ℕ} (r : Reward S A B) (γ Cb δ : ℝ)
    (D : Fin N → Sample S A B) (t : ℕ) : Fin S → Fin A → Fin B → ℝ :=
  (Tplus r γ Cb δ D)^[t] (fun _ _ _ => 1 / (1 - γ))

/-- The number of iterations `T = ⌈log(N/(1−γ)) / log(1/γ)⌉` (Algorithm 1,
arXiv:2206.04044v2, p.9). -/
noncomputable def horizon (N : ℕ) (γ : ℝ) : ℕ :=
  ⌈Real.log ((N : ℝ) / (1 - γ)) / Real.log (1 / γ)⌉₊

/-- `Q⁻_pe = Q⁻_{pe,T}` (arXiv:2206.04044v2, (3.9), p.8). -/
noncomputable def QpeMinus {S A B N : ℕ} (r : Reward S A B) (γ Cb δ : ℝ)
    (D : Fin N → Sample S A B) : Fin S → Fin A → Fin B → ℝ :=
  QminusIter r γ Cb δ D (horizon N γ)

/-- `Q⁺_pe = Q⁺_{pe,T}` (arXiv:2206.04044v2, (3.9), p.8). -/
noncomputable def QpePlus {S A B N : ℕ} (r : Reward S A B) (γ Cb δ : ℝ)
    (D : Fin N → Sample S A B) : Fin S → Fin A → Fin B → ℝ :=
  QplusIter r γ Cb δ D (horizon N γ)

/-- `V⁻_pe`, the value function (3.3) of `Q⁻_pe` (arXiv:2206.04044v2, p.15; Algorithm 1, p.9). -/
noncomputable def VpeMinus {S A B N : ℕ} (r : Reward S A B) (γ Cb δ : ℝ)
    (D : Fin N → Sample S A B) : Fin S → ℝ :=
  Vof (QpeMinus r γ Cb δ D)

/-- `V⁺_pe`, the value function (3.3) of `Q⁺_pe` (arXiv:2206.04044v2, p.15; Algorithm 1, p.9). -/
noncomputable def VpePlus {S A B N : ℕ} (r : Reward S A B) (γ Cb δ : ℝ)
    (D : Fin N → Sample S A B) : Fin S → ℝ :=
  Vof (QpePlus r γ Cb δ D)

/-- The output of Algorithm 1 (arXiv:2206.04044v2, p.9; (3.10), p.8): `(μ̂, ν̂) = (μ⁻_T, ν⁺_T)`
is an output when, for every state `s`, `μ̂(s)` is the max-player part of a solution of the
matrix game `Q⁻_{pe,T}(s, ·, ·)` and `ν̂(s)` is the min-player part of a solution of the matrix
game `Q⁺_{pe,T}(s, ·, ·)`.

**Formalization Note.** `MatrixNash(M)` "returns a solution `(ŵ, ẑ)` to the minimax program
`max_w min_z w⊤Mz`", i.e. a saddle point of `w⊤Mz` on `Δ(A) × Δ(B)`
(`TheoryOfGames.Minimax.IsMixedSaddlePoint`). The algorithm does not fix which solution is
returned, so every pair satisfying this predicate is an output; saddle points exist by the
minimax theorem, so the predicate is satisfiable. -/
def IsVILCBOutput {S A B N : ℕ} (r : Reward S A B) (γ Cb δ : ℝ) (D : Fin N → Sample S A B)
    (μh : Policy S A) (νh : Policy S B) : Prop :=
  ∀ s, (∃ z : Fin B → ℝ,
          TheoryOfGames.Minimax.IsMixedSaddlePoint (QpeMinus r γ Cb δ D s) (μh s) z) ∧
       (∃ w : Fin A → ℝ,
          TheoryOfGames.Minimax.IsMixedSaddlePoint (QpePlus r γ Cb δ D s) w (νh s))

/-- The penalty averaged over a product policy,
`β^{μ,ν}(s) = E_{a∼μ(s), b∼ν(s)}[β(s, a, b; W)]` (arXiv:2206.04044v2, (B.15b), p.17, with
`W = V⁻_pe`). -/
noncomputable def betaPol {S A B N : ℕ} (γ Cb δ : ℝ) (D : Fin N → Sample S A B)
    (μ : Policy S A) (ν : Policy S B) (W : Fin S → ℝ) : Fin S → ℝ :=
  fun s => ∑ a, ∑ b, (μ s : Fin A → ℝ) a * (ν s : Fin B → ℝ) b * beta γ Cb δ D s a b W

end OfflineZeroSumMG



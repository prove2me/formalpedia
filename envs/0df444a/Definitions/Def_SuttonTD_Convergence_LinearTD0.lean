-- Prove2me | Definitions.Def_SuttonTD_Convergence_LinearTD0
-- name    : SuttonTD_Convergence_LinearTD0
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T06:38:27.520112+00:00
-- url     : https://prove2.me/theorems/bd44bc32-94db-4e77-8ae6-2c8d49b5e127
-- title:
--   Linear TD(0) with weight updates after each sequence
-- statement:
--   Each nonterminal state $i$ has an observation vector $x_i\in\mathbb R^K$, and the prediction at time $t$ is linear, $P_t=w^\top x_{q_t}$. For an episode with nonterminal states $q_1,\dots,q_m$ and outcome $z$, set $P_{m+1}=z$. **Linear TD(0)** with weight updates after each sequence, step size $\alpha$, changes the weight vector by
--
--   $$w\;\leftarrow\;w+\sum_{t=1}^{m}\alpha\,(P_{t+1}-P_t)\,x_{q_t},$$
--
--   where $w$ is held fixed during the sequence. Starting from an initial weight vector $w_0$, the weight vector after $n$ sequences is $w_n$, with $w_{n+1}$ obtained from $w_n$ by this update applied to the $(n+1)$-st sequence.
--
--   This is the learning procedure whose convergence Theorem 2 establishes.
--
--   **Formalization Note** `tdWeights x α w₀ e n ω` is $w_n$; sequences are indexed from $0$, so $w_{n+1}$ uses `e n ω`.
-- source:
--   Sutton (1988), Machine Learning 3:9–44, §4.1, p. 25 (PDF p. 17), first display of the proof of Theorem 2; (4) with λ = 0, p. 15; p. 13

import Definitions.Def_SuttonTD_Convergence_EpisodeModel

namespace SuttonTD.Convergence

variable {N T : Type*} {K : ℕ}

/-- The total weight change of linear TD(0) over one sequence (Sutton 1988, §4.1, p. 25,
PDF p. 17, first display of the proof of Theorem 2; definition (4) with `λ = 0`, p. 15):
for the nonterminal states `q_1, …, q_m`, outcome `z`, observation vectors `x_i` and the weight
vector `w`, which is held fixed during the sequence,
`∑_{t=1}^{m} α (P_{t+1} − P_t) x_{q_t}`, where `P_t = wᵀ x_{q_t}` and `P_{m+1} = z`. -/
def tdIncrement (x : N → Fin K → ℝ) (α : ℝ) (w : Fin K → ℝ) : List N → ℝ → (Fin K → ℝ)
  | [], _ => 0
  | [i], z => (α * (z - w ⬝ᵥ x i)) • x i
  | i :: k :: rest, z => (α * (w ⬝ᵥ x k - w ⬝ᵥ x i)) • x i + tdIncrement x α w (k :: rest) z

/-- One update of linear TD(0) "with weight updates after each sequence" (p. 24):
`w ↦ w + ∑_{t=1}^{m} α (P_{t+1} − P_t) x_{q_t}` for the episode `e`. -/
def tdStep (x : N → Fin K → ℝ) (α : ℝ) (e : Episode N T) (w : Fin K → ℝ) : Fin K → ℝ :=
  w + tdIncrement x α w e.path e.out

/-- `tdWeights x α w₀ e n ω` is the weight vector `w_n` after the first `n` sequences
`e 0 ω, …, e (n-1) ω` have been experienced, starting from the initial weight vector `w₀`
(p. 25: "`w_n` denotes the weight vector after `n` sequences have been experienced").

Formalization Note: episodes are indexed from `0`, so the paper's `w_{n+1}` (computed from the
`(n+1)`-st sequence) is `tdStep x α (e n ω) (w_n)`. -/
def tdWeights {Ω : Type*} (x : N → Fin K → ℝ) (α : ℝ) (w₀ : Fin K → ℝ)
    (e : ℕ → Ω → Episode N T) : ℕ → Ω → (Fin K → ℝ)
  | 0, _ => w₀
  | n + 1, ω => tdStep x α (e n ω) (tdWeights x α w₀ e n ω)

end SuttonTD.Convergence



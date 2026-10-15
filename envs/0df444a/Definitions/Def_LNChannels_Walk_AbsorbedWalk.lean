-- Prove2me | Definitions.Def_LNChannels_Walk_AbsorbedWalk
-- name    : LNChannels_Walk_AbsorbedWalk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:00.670303+00:00
-- url     : https://prove2.me/theorems/cafb529f-81dd-4656-9b7f-b972ae18f37b
-- title:
--   The channel balance as a random walk absorbed when either side is exhausted (Proposition 1)
-- statement:
--   Consider a payment channel in which node 1 has committed $l_1\ge 1$ units and node 2 has committed $l_2\ge 1$ units. Node 1 pays node 2 one unit at the jumps of a Poisson process of rate $\lambda_1$, and node 2 pays node 1 at rate $\lambda_2$, independently. The **balance** $X$ starts at $0$, increases by one when node 2 pays and decreases by one when node 1 pays. Node 2 has exhausted its side when $X=l_2$, node 1 when $X=-l_1$.
--
--   Observed at its jumps, the balance is a random walk on $\{-l_1,\dots,l_2\}$: from an interior balance $-l_1<n<l_2$ it moves to $n+1$ with probability $\lambda_2/(\lambda_1+\lambda_2)$ and to $n-1$ with probability $\lambda_1/(\lambda_1+\lambda_2)$. In this definition the two exhaustion balances $-l_1$ and $l_2$ are **absorbing**. The transition matrix is
--   $$
--   P(n,n')=\begin{cases}\mathbf 1\{n'=n\}, & n\in\{-l_1,l_2\},\\ \lambda_2/(\lambda_1+\lambda_2), & -l_1<n<l_2,\ n'=n+1,\\ \lambda_1/(\lambda_1+\lambda_2), & -l_1<n<l_2,\ n'=n-1,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   The file also names the state of the initial balance $0$.
--
--   The walk describes the question of Proposition 1: which node exhausts the channel first. For $\lambda_1=\lambda_2$ it is the classical gambler's ruin chain on $\{0,\dots,l_1+l_2\}$.
--
--   **Formalization Note** The states are `Fin (l₁ + l₂ + 1)`, and index $i$ stands for the balance $i-l_1$. Index $0$ is $-l_1$, index $l_1$ (`absorbedStart`) is the initial balance $0$, and `Fin.last (l₁ + l₂)` is $l_2$. The matrix has the same `if … then … else` shape as the platform's `MarkovMixing.gamblersChain`. It is a stochastic matrix whenever $\lambda_1,\lambda_2\ge0$ and $\lambda_1+\lambda_2>0$. The rates are written `lam₁ lam₂`, because `λ` is a Lean keyword.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 8 (PDF 9), Proposition 1; p. 13 (PDF 14), proof of Proposition 1

import Mathlib

namespace LNChannels.Walk

/-- The channel balance as a walk absorbed at exhaustion (Proposition 1, p. 8; proof, p. 13).
States `Fin (l₁ + l₂ + 1)`, index `i` ↔ balance `i − l₁`: index `0` is `−l₁` (node 1 has
exhausted its side), index `l₁` is the initial balance `0`, `Fin.last (l₁ + l₂)` is `+l₂` (node 2
has exhausted its side). An interior state moves up (node 2 pays) with probability
`lam₂ / (lam₁ + lam₂)` and down (node 1 pays) with probability `lam₁ / (lam₁ + lam₂)`; the two
ends are absorbing. Same shape as `MarkovMixing.gamblersChain (l₁ + l₂)`. -/
noncomputable def absorbedWalk (lam₁ lam₂ : ℝ) (l₁ l₂ : ℕ) :
    Matrix (Fin (l₁ + l₂ + 1)) (Fin (l₁ + l₂ + 1)) ℝ :=
  fun k l =>
    if k = 0 ∨ k = Fin.last (l₁ + l₂) then (if l = k then 1 else 0)
    else if l.val = k.val + 1 then lam₂ / (lam₁ + lam₂)
    else if l.val + 1 = k.val then lam₁ / (lam₁ + lam₂)
    else 0

/-- The index of the initial balance `0` in the absorbed walk. -/
def absorbedStart (l₁ l₂ : ℕ) : Fin (l₁ + l₂ + 1) :=
  ⟨l₁, by omega⟩

end LNChannels.Walk



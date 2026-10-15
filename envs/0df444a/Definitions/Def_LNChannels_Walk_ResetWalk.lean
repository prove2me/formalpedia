-- Prove2me | Definitions.Def_LNChannels_Walk_ResetWalk
-- name    : LNChannels_Walk_ResetWalk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:59.668709+00:00
-- url     : https://prove2.me/theorems/1c83da43-176b-45b0-86e4-f7b43f4424da
-- title:
--   The channel balance with resets, its occupation masses m(n) and the on-chain fraction (Proposition 2)
-- statement:
--   Consider the channel of Proposition 2: node 1 has committed $l_1\ge1$ units and node 2 has committed $l_2\ge1$. Each channel transaction is a payment from node 2 to node 1 with probability $p=\lambda_2/(\lambda_1+\lambda_2)$, which moves the balance $X$ up by one, or a payment from node 1 to node 2 with probability $1-p=\lambda_1/(\lambda_1+\lambda_2)$, which moves it down by one. When the balance reaches $l_2$ or $-l_1$, one side of the channel is exhausted. The channel is then closed and reopened by an on-chain transaction, and the balance is **immediately reset to $0$**.
--
--   The balance therefore lives on the interior balances $\{-l_1+1,\dots,l_2-1\}$, and the **reset walk** has transition probabilities
--   $$
--   P(n,\cdot)=p\,\delta_{u(n)}+(1-p)\,\delta_{d(n)},\qquad u(n)=\begin{cases}n+1,&n+1<l_2\\0,&n+1=l_2\end{cases},\quad d(n)=\begin{cases}n-1,&n-1>-l_1\\0,&n-1=-l_1.\end{cases}
--   $$
--   When both moves land on the same balance, as can happen for $l_1=1$ or $l_2=1$, the two probabilities add.
--
--   For a vector $m$ on these states, $m(n)$ denotes its mass at the balance $n\in\mathbb Z$. As in the paper, $m(n)=0$ at the balances $n\le -l_1$ and $n\ge l_2$, which the reset walk never occupies; in particular $m(l_2)=m(-l_1)=0$. The **on-chain fraction** of $m$ is
--   $$
--   m(l_2-1)\,\frac{\lambda_2}{\lambda_1+\lambda_2}+m(-l_1+1)\,\frac{\lambda_1}{\lambda_1+\lambda_2}.
--   $$
--   When $m$ is a stationary distribution, this is the long-run fraction of channel transactions that trigger an on-chain transaction: the up-moves from $l_2-1$ and the down-moves from $-l_1+1$.
--
--   These objects state Proposition 2 and the steps (28)–(30) of its proof.
--
--   **Formalization Note** The states are `Fin (l₁ + l₂ - 1)`, and index $j$ stands for the balance $j+1-l_1$. The bottom balance $-l_1+1$ is index $0$, the balance $0$ is index $l_1-1$, and the top balance $l_2-1$ is index $l_1+l_2-2$. The helpers `upTarget` and `downTarget` give the index reached by each move. `massAt l₁ l₂ m n` is $m(n)$, and `resetFraction` is the on-chain fraction. Neither the stationary distribution nor the ratio is defined by a closed form: $m$ is any vector, and the theorems quantify over stationary ones.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 13 (PDF 14), proof of Proposition 2, (27)–(30) and the display after (30)

import Mathlib

namespace LNChannels.Walk

/-- Index (in `Fin (l₁ + l₂ - 1)`) reached by an up-move from index `j` of the reset walk:
`j + 1`, except that the move from the top balance `l₂ − 1` reaches `l₂` and is reset to the
balance `0`, whose index is `l₁ − 1`. -/
def upTarget (l₁ l₂ j : ℕ) : ℕ :=
  if j + 1 = l₁ + l₂ - 1 then l₁ - 1 else j + 1

/-- Index reached by a down-move from index `j` of the reset walk: `j − 1`, except that the
move from the bottom balance `−l₁ + 1` (index `0`) reaches `−l₁` and is reset to the balance `0`,
whose index is `l₁ − 1`. -/
def downTarget (l₁ j : ℕ) : ℕ :=
  if j = 0 then l₁ - 1 else j - 1

/-- The channel balance with resets (proof of Proposition 2, p. 13). The balance lives on the
interior balances `n ∈ {−l₁ + 1, …, l₂ − 1}`, as `Fin (l₁ + l₂ - 1)` with index `j` ↔ balance
`j + 1 − l₁`. Each channel transaction is an up-move (node 2 pays) with probability
`lam₂ / (lam₁ + lam₂)` or a down-move (node 1 pays) with probability `lam₁ / (lam₁ + lam₂)`;
a move that reaches `l₂` or `−l₁` exhausts the channel, which is immediately reset to the
balance `0`. The two contributions add when both moves land on the same state. -/
noncomputable def resetWalk (lam₁ lam₂ : ℝ) (l₁ l₂ : ℕ) :
    Matrix (Fin (l₁ + l₂ - 1)) (Fin (l₁ + l₂ - 1)) ℝ :=
  fun i k =>
    (if k.val = upTarget l₁ l₂ i.val then lam₂ / (lam₁ + lam₂) else 0) +
    (if k.val = downTarget l₁ i.val then lam₁ / (lam₁ + lam₂) else 0)

/-- `m(n)`: the mass that a vector `m` on the states of the reset walk puts on the balance
`n ∈ ℤ`, with the paper's convention `m(n) = 0` for the balances `n ≤ −l₁` and `n ≥ l₂`, which the
reset walk never occupies (p. 13: "m(l₂) = 0", "m(−l₁) = 0 by construction"). -/
def massAt (l₁ l₂ : ℕ) (m : Fin (l₁ + l₂ - 1) → ℝ) (n : ℤ) : ℝ :=
  if h : -(l₁ : ℤ) < n ∧ n < (l₂ : ℤ) then m ⟨(n + l₁ - 1).toNat, by omega⟩ else 0

/-- The fraction of channel transactions that trigger an on-chain transaction under the
distribution `m` (p. 13): the up-moves from `l₂ − 1` and the down-moves from `−l₁ + 1`,
`m(l₂ − 1) λ₂/(λ₁ + λ₂) + m(−l₁ + 1) λ₁/(λ₁ + λ₂)`. -/
noncomputable def resetFraction (lam₁ lam₂ : ℝ) (l₁ l₂ : ℕ) (m : Fin (l₁ + l₂ - 1) → ℝ) : ℝ :=
  massAt l₁ l₂ m ((l₂ : ℤ) - 1) * (lam₂ / (lam₁ + lam₂)) +
    massAt l₁ l₂ m (-(l₁ : ℤ) + 1) * (lam₁ / (lam₁ + lam₂))

end LNChannels.Walk



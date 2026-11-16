-- Prove2me | Definitions.Def_CSPSubsample_Supplement_FreeGame
-- name    : CSPSubsample_Supplement_FreeGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:53:19.885243+00:00
-- url     : https://prove2.me/theorems/2a23bfe0-da2c-4713-acc6-295727b1d5f7
-- title:
--   $k$-player free game $G=((Y_i),(B_i),V)$ and its value $\omega(G)$
-- statement:
--   A **$k$-player free game** $G=((Y_i)_{i\in[k]},(B_i)_{i\in[k]},V)$ consists of finite question sets $Y_1,\dots,Y_k$, finite answer sets $B_1,\dots,B_k$, and a payoff function
--   $$
--   V:Y_1\times\cdots\times Y_k\times B_1\times\cdots\times B_k\to[0,1].
--   $$
--   A **strategy profile** is a tuple of functions $(b_i:Y_i\to B_i)_{i\in[k]}$: player $i$ answers $b_i(y_i)$ to the question $y_i$. The questions are drawn independently and uniformly, one for each player, and the **value** of the game is the best expected payoff,
--   $$
--   \omega(G)=\max_{(b_i:Y_i\to B_i)_{i\in[k]}}\ \mathbb E_{y_i\sim Y_i}\big[V(y_1,\dots,y_k,b_1(y_1),\dots,b_k(y_k))\big].
--   $$
--
--   Free games are the optimization problem faced by the $k$ non-communicating provers of the class AM($k$) of Aaronson, Impagliazzo and Moshkovitz; the subsampling theorem for free games (Theorem 6.1) is stated in terms of $\omega$.
--
--   **Formalization Note** Players are `Fin k`. The question and answer sets are finite and nonempty (the uniform question and the maximum over strategies are undefined otherwise). The expected payoff is the finite average over all question profiles, of which there are $|Y_1|\cdots|Y_k|$; the maximum is a real supremum over the finite, nonempty set of strategy profiles of values in $[0,1]$, hence attained.
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), Definition 1.2 (FreeGame), p.2 (PDF p.4)

import Mathlib

set_option autoImplicit false

namespace CSPSubsample.Supplement

/-- A **k-player free game** `G = ((Y_i)_{i∈[k]}, (B_i)_{i∈[k]}, V)` (Bernasconi, Castiglioni,
Celli, Farina, Malavolta, *A Subsampling Theorem for Constraint Satisfaction Problems with Large
Arity*, arXiv:2608.00203 (PDF sha256 fd9ae011…), Definition 1.2 (FreeGame), p.2 = PDF p.4):
finite question sets `Y_i`, finite answer sets `B_i`, and a payoff
`V : Y_1 × ⋯ × Y_k × B_1 × ⋯ × B_k → [0,1]`.

**Formalization Note** Players are `Fin k` (paper index `i` is Lean index `i − 1`). A question
profile `(y_1, …, y_k)` is a dependent function `(i : Fin k) → Y i`, an answer profile likewise,
and `V y b` is `V(y_1, …, y_k, b_1, …, b_k)`. The sets `Y_i`, `B_i` are finite and **nonempty**
(the fields `nonemptyY`, `nonemptyB`): the uniform question `y_i ∼ Y_i` and the maximum over
strategies `b_i : Y_i → B_i` in the value `ω(G)` are undefined otherwise. The bounds
`0 ≤ V ≤ 1` are fields. -/
structure FreeGame (k : ℕ) where
  /-- The question set `Y_i` of player `i`. -/
  Y : Fin k → Type
  /-- The answer set `B_i` of player `i`. -/
  B : Fin k → Type
  /-- `Y_i` is finite. -/
  fintypeY : ∀ i, Fintype (Y i)
  /-- `B_i` is finite. -/
  fintypeB : ∀ i, Fintype (B i)
  /-- `Y_i` is nonempty. -/
  nonemptyY : ∀ i, Nonempty (Y i)
  /-- `B_i` is nonempty. -/
  nonemptyB : ∀ i, Nonempty (B i)
  /-- The payoff `V(y_1, …, y_k, b_1, …, b_k)`. -/
  V : ((i : Fin k) → Y i) → ((i : Fin k) → B i) → ℝ
  /-- `0 ≤ V`. -/
  V_nonneg : ∀ y b, 0 ≤ V y b
  /-- `V ≤ 1`. -/
  V_le_one : ∀ y b, V y b ≤ 1

attribute [instance] FreeGame.fintypeY FreeGame.fintypeB FreeGame.nonemptyY FreeGame.nonemptyB

namespace FreeGame

variable {k : ℕ}

/-- The expected payoff of the strategy profile `b = (b_i : Y_i → B_i)_{i∈[k]}` when the
questions `y_i ∼ Y_i` are independent and uniform:
`E_{y_i∼Y_i}[V(y_1, …, y_k, b_1(y_1), …, b_k(y_k))] = (1/|Y_1|⋯|Y_k|) ∑_y V(y, (b_i(y_i))_i)`
(arXiv:2608.00203 (PDF sha256 fd9ae011…), Definition 1.2, p.2 = PDF p.4).

**Formalization Note** The expectation over independent uniform questions is the finite
average over all question profiles `(i : Fin k) → Y i`, whose number is `|Y_1|⋯|Y_k|`. -/
noncomputable def payoff (G : FreeGame k) (b : (i : Fin k) → G.Y i → G.B i) : ℝ :=
  (∑ y : (i : Fin k) → G.Y i, G.V y (fun i => b i (y i))) /
    (Fintype.card ((i : Fin k) → G.Y i) : ℝ)

/-- The **value** of the free game, `ω(G) := max_{(b_i : Y_i → B_i)_{i∈[k]}}
E_{y_i∼Y_i}[V(y_1, …, y_k, b_1(y_1), …, b_k(y_k))]` (arXiv:2608.00203 (PDF sha256 fd9ae011…),
Definition 1.2, p.2 = PDF p.4).

**Formalization Note** The maximum is a real `⨆` over all strategy profiles
`(i : Fin k) → Y i → B i`. The index type is nonempty (every `B_i` is nonempty) and finite, and
every `payoff` lies in `[0,1]`, so the supremum is attained and equals the paper's maximum. -/
noncomputable def value (G : FreeGame k) : ℝ :=
  ⨆ b : (i : Fin k) → G.Y i → G.B i, G.payoff b

end FreeGame

end CSPSubsample.Supplement



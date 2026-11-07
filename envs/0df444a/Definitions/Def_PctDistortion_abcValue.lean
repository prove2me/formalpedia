-- Prove2me | Definitions.Def_PctDistortion_abcValue
-- name    : PctDistortion_abcValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:49.350205+00:00
-- url     : https://prove2.me/theorems/3f4fa0fc-4ef6-4230-8dc5-37b5b2146982
-- title:
--   The ABC game on a digraph and its value
-- statement:
--   The **asymmetrically biased Condorcet (ABC) game** on a simple digraph $G=(V,E)$ is the zero-sum game in which Alice and Bob choose nodes $a,b\in V$ and Alice receives
--   $$p^{ABC}_A(a,b)=\begin{cases}-1&\text{if }(b,a)\in E,\\ +1&\text{otherwise,}\end{cases}$$
--   and Bob the opposite. Alice wins unless Bob's node has an arc to hers; in particular she wins when both choose the same node. The **value** $\nu(\mathcal G^{ABC}_G)$ is Alice's payoff at any mixed Nash equilibrium.
--
--   **Formalization Note** Mixed strategies, payoffs and equilibria are those of the published finite zero-sum game `BlottoLP.Flow`. The value is defined as Alice's maximin value $\sup_{a\in\Delta V}\min_{b\in V}\sum_u a_u\,p^{ABC}_A(u,b)$, which by the minimax theorem is her payoff at every equilibrium.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Definition 4, p.10; value p.11

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum

set_option autoImplicit false

namespace PctDistortion

open Classical in
/-- Alice's payoff in the **asymmetrically biased Condorcet (ABC) game** on the digraph `G` when
Alice plays node `a` and Bob plays node `b`: `-1` if `(b, a)` is an arc of `G`, `+1`
otherwise. Bob receives the opposite payoff (zero-sum).

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Definition 4, p.10: "The asymmetrically biased Condorcet (ABC) game over a simple digraph
G = (V, E), denoted by G^ABC_G, is a zero-sum game in which Alice and Bob choose nodes a, b ∈ V,
respectively. Alice's payoff is p^ABC_A(a, b) = −1 if (b, a) ∈ E, +1 otherwise. Bob receives the
opposite payoff −p^ABC_A(a, b)."

**Formalization Note.** Mixed strategies, expected payoffs and Nash equilibria are those of the
published finite zero-sum game `BlottoLP.Flow` (`IsMixed`, `expPay`, `IsNashEq`), with Alice
as the row player. -/
noncomputable def abcPayoff {W : Type} (G : Digraph W) (a b : W) : ℝ :=
  if G.Adj b a then -1 else 1

/-- The **maximin value** of a finite zero-sum game with row payoff `M`:
`sup_{σ mixed} min_b Σ_a σ(a) M(a, b)`, the largest payoff the row player can guarantee against
every pure strategy of the column player. -/
noncomputable def maximinValue {α β : Type} [Fintype α] (M : α → β → ℝ) : ℝ :=
  ⨆ σ : {σ : α → ℝ // BlottoLP.Flow.IsMixed σ}, ⨅ b, ∑ a, σ.1 a * M a b

/-- The **value** `ν(G^ABC_G)` of the ABC game on `G`.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), p.11: "Because the game is zero-sum, all (mixed) Nash equilibria give the same payoff to Alice
(and hence to Bob), and we consider Alice's payoff under any of the equilibrium strategies the value
of the game ν(G^ABC_G)."

**Formalization Note.** The value is defined as Alice's maximin value, which exists for every
finite game; by the minimax theorem it equals Alice's expected payoff at every mixed Nash
equilibrium, the paper's definition. The supremum is over a nonempty set (for a nonempty node type)
of values bounded by `1`. -/
noncomputable def abcValue {W : Type} [Fintype W] (G : Digraph W) : ℝ :=
  maximinValue (abcPayoff G)

end PctDistortion



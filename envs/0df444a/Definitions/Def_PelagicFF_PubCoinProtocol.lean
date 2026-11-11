-- Prove2me | Definitions.Def_PelagicFF_PubCoinProtocol
-- name    : PelagicFF_PubCoinProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:45.644769+00:00
-- url     : https://prove2.me/theorems/0c7e0961-b489-4f82-9cfd-d6b3fab7c61a
-- title:
--   Randomized public-coin two-way protocols, their cost and success probability
-- statement:
--   A **randomized public-coin two-way protocol** with input sets $X$ (Alice), $Y$ (Bob) and output set $Z$ is a probability law over a finite set of coin values $r$ together with, for each $r$, a deterministic two-party protocol tree: every inner node belongs to Alice or Bob and carries a bit-valued function of that player's input, and every leaf $\tau$ carries Bob's output function $y_\tau:Y\to Z$. On coin $r$ and inputs $(x,y)$ the players walk to a leaf $\tau$ and Bob outputs $y_\tau(y)$.
--
--   - The **cost** is the largest number of bits sent: the maximum depth of the trees over coin values of positive probability.
--   - The **success probability** on $(x,y)$ for a relation $R$ is the coin probability that Bob's output lies in $R(x,y)$.
--   - The **average success probability** is the mean of the success probability over uniformly random $(x,y)\in X\times Y$.
--
--   This is the classical model of the lower bound in Theorem 4.2; Bob's output depends on the transcript and on his own input, as on p.30.
--
--   **Formalization Note** Trees are the published `OneOfManyCC.Protocol` with leaf label type `Y → Z`. Private coins are subsumed by public coins.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §2.1, p.14; Theorem 4.2, p.27; §4.2.2, p.30

import Mathlib
import Definitions.Def_OneOfManyCC_Protocol

namespace PelagicFF

/-- **Randomized public-coin two-way protocol** with Bob as the output player.

arXiv:2610.05585 (held version, sha256 4564aef3…), §2.1, p.14 and Theorem 4.2, p.27 ("randomized
public-coin (two-way) communication protocol"); §4.2.2, p.30: a public-coin protocol is a
distribution over deterministic protocols (Yao's principle), and in a deterministic protocol "Bob's
output on seeing transcript τ is determined by a function of his input y_τ : B_τ → {0,1}ⁿ".

A finite coin type `Coin` with law `coin`, and for each coin value a deterministic two-party tree
(published `OneOfManyCC.Protocol`) whose leaves are labelled by Bob's output function `Y → Z`.

**Formalization Note.** Leaves carry functions `Y → Z`, so Bob's output may depend on his input and
the transcript, exactly as on p.30; a leaf label fixed by the transcript alone would admit fewer
protocols. Private coins are subsumed by public coins. -/
structure PubCoinProtocol (X Y Z : Type) where
  /-- The public-coin space. -/
  Coin : Type
  /-- The public-coin space is finite. -/
  [coinFintype : Fintype Coin]
  /-- The law of the public coins. -/
  coin : PMF Coin
  /-- The deterministic protocol run on coin value `r`. -/
  tree : Coin → OneOfManyCC.Protocol X Y (Y → Z)

attribute [instance] PubCoinProtocol.coinFintype

namespace PubCoinProtocol

variable {X Y Z : Type}

/-- Bob's output on coins `r` and inputs `(x, y)`: the leaf function reached, applied to `y`. -/
def output (P : PubCoinProtocol X Y Z) (r : P.Coin) (x : X) (y : Y) : Z :=
  (P.tree r).eval x y y

/-- The communication cost: the largest number of bits sent, over all inputs and over all coin
values of positive probability (the depth of the deterministic trees run with positive
probability). The public coins themselves are free. -/
noncomputable def cost (P : PubCoinProtocol X Y Z) : ℕ := by
  classical
  exact (Finset.univ.filter (fun r => P.coin r ≠ 0)).sup (fun r => (P.tree r).depth)

/-- Success probability on the input `(x, y)`: the coin mass of the coin values on which Bob's
output lies in `R(x, y)`. -/
noncomputable def succProb (P : PubCoinProtocol X Y Z) (R : X → Y → Z → Prop) (x : X) (y : Y) : ℝ := by
  classical
  exact ∑ r, if R x y (P.output r x y) then (P.coin r).toReal else 0

/-- Average success probability under the uniform input distribution on `X × Y`. -/
noncomputable def avgSucc [Fintype X] [Fintype Y] (P : PubCoinProtocol X Y Z)
    (R : X → Y → Z → Prop) : ℝ :=
  ((Fintype.card X : ℝ) * Fintype.card Y)⁻¹ * ∑ x, ∑ y, P.succProb R x y

end PubCoinProtocol

end PelagicFF



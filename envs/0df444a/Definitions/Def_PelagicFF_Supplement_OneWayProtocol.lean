-- Prove2me | Definitions.Def_PelagicFF_Supplement_OneWayProtocol
-- name    : PelagicFF_Supplement_OneWayProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:24:30.982036+00:00
-- url     : https://prove2.me/theorems/d46e33e8-efe4-4683-97b8-f369f1541ab4
-- title:
--   Randomized public-coin one-way protocols with $c$-bit messages
-- statement:
--   A **randomized public-coin one-way protocol** with input sets $X$ (Alice), $Y$ (Bob), output set $Z$ and message length $c$ consists of
--
--   1. a finite set of coin values $r$ with a probability law $\Pr[r]$ (the public coins, seen by both players);
--   2. for every coin value $r$ and Alice input $x$, a message $\mathrm{msg}_r(x)\in\{0,1\}^c$, a string of exactly $c$ bits;
--   3. for every coin value $r$, message $m$ and Bob input $y$, an output $\mathrm{out}_r(m,y)\in Z$.
--
--   Its communication cost is $c$. For a relation $R$ (Bob must output $z\in R(x,y)$), the success probability on the input $(x,y)$ is
--
--   $$
--   \mathrm{succ}(x,y)=\sum_{r}\Pr[r]\,\mathbf 1\big[\mathrm{out}_r(\mathrm{msg}_r(x),y)\in R(x,y)\big],
--   $$
--
--   and, for finite $X$ and $Y$, the average success probability under the uniform input law is $\frac1{|X||Y|}\sum_{x,y}\mathrm{succ}(x,y)$.
--
--   This is the model of the randomized one-way lower bounds of Theorems 5.2, 6.2, 6.4 and A.10. A $c$-bit message takes at most $2^c$ values, as the proofs on pp.45 and 60 use.
--
--   **Formalization Note** Messages are `Fin c → Bool`. Private randomness is subsumed by the public coins. When $x$ and $y$ are drawn independently and uniformly, their joint law is the uniform law on $X\times Y$, which is what `avgSucc` averages over.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §2.1, p.14; p.45 ("a c-bit message takes at most 2^c values"); p.60

import Mathlib

namespace PelagicFF.Supplement

/-- **Randomized public-coin one-way protocol with `c`-bit messages.**

Anselm, Ding, Gilboa, Grewal, *Optimal and Verifiable Quantum Advantages in Communication
Complexity*, arXiv:2610.05585 (held version, sha256 4564aef3…), §2.1, p.14: "We write … R¹ε(P) …
for the minimum costs of … randomized classical one-way … protocols for a problem P … In all
communication models we consider, the players have access to shared randomness"; p.45 and p.60:
"a c-bit message takes at most 2^c values", Alice's message is a function `msg : X → F₂^c` of her
input, and Bob's output is a function of the message and his input.

Fields: a finite public-coin type `Coin` with law `coin`; Alice's message `msg r x`, a string of
exactly `c` bits, on coins `r` and input `x`; Bob's output `out r m y` on coins `r`, message `m`
and input `y`. The communication cost is `c`.

**Formalization Note.** Messages are fixed-length strings `Fin c → Bool` (`2^c` values), as the
proofs on pp.45 and 60 use. Private randomness is subsumed by the public coins. -/
structure OneWayProtocol (X Y Z : Type) (c : ℕ) where
  /-- The public-coin space. -/
  Coin : Type
  /-- The public-coin space is finite. -/
  [coinFintype : Fintype Coin]
  /-- The law of the public coins. -/
  coin : PMF Coin
  /-- Alice's `c`-bit message on coins `r` and input `x`. -/
  msg : Coin → X → (Fin c → Bool)
  /-- Bob's output on coins `r`, message `m` and input `y`. -/
  out : Coin → (Fin c → Bool) → Y → Z

attribute [instance] OneWayProtocol.coinFintype

namespace OneWayProtocol

variable {X Y Z : Type} {c : ℕ}

/-- Success probability of `P` for the relation `R` on the input `(x, y)`: the coin mass of the
coin values on which Bob's output lies in `R(x, y)`. -/
noncomputable def succProb (P : OneWayProtocol X Y Z c) (R : X → Y → Z → Prop) (x : X) (y : Y) : ℝ := by
  classical
  exact ∑ r, if R x y (P.out r (P.msg r x) y) then (P.coin r).toReal else 0

/-- Average success probability under the uniform input distribution on `X × Y` (equivalently,
`x` and `y` independent and uniform). -/
noncomputable def avgSucc [Fintype X] [Fintype Y] (P : OneWayProtocol X Y Z c)
    (R : X → Y → Z → Prop) : ℝ :=
  ((Fintype.card X : ℝ) * Fintype.card Y)⁻¹ * ∑ x, ∑ y, P.succProb R x y

end OneWayProtocol

end PelagicFF.Supplement



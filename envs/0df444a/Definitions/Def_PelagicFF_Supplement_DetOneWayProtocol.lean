-- Prove2me | Definitions.Def_PelagicFF_Supplement_DetOneWayProtocol
-- name    : PelagicFF_Supplement_DetOneWayProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:24:46.367319+00:00
-- url     : https://prove2.me/theorems/2b1f56db-93c5-41ec-ad1a-b7294fb84b1d
-- title:
--   Deterministic one-way protocols with $c$-bit messages and exactness
-- statement:
--   A **deterministic one-way protocol** with input sets $X$ (Alice), $Y$ (Bob), output set $Z$ and message length $c$ consists of Alice's message map $\mathrm{msg}:X\to\{0,1\}^c$ and Bob's output map $\mathrm{out}:\{0,1\}^c\times Y\to Z$. Its communication cost is $c$.
--
--   It is **exact** for a relation $R$ (succeeds with probability $1$) when
--
--   $$
--   \mathrm{out}(\mathrm{msg}(x),y)\in R(x,y)\qquad\text{for every }(x,y)\in X\times Y.
--   $$
--
--   This is the model of Theorem A.8 and of the exact classical upper bounds of Theorems 6.2 and A.2.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), p.45 (deterministic c-bit protocol, msg : V_{n,d} → F₂^c); p.59 (msg : F₂^N → F₂^c)

import Mathlib

namespace PelagicFF.Supplement

/-- **Deterministic one-way protocol with `c`-bit messages.**

arXiv:2610.05585 (held version, sha256 4564aef3…), p.45 ("Fix some deterministic c-bit protocol Π
… Alice's message is a function of her input q which we denote by msg : V_{n,d} → F₂^c. Given a
message m … and nonzero direction a, Bob outputs a fixed pair") and p.59 ("Define msg : F₂^N → F₂^c
via msg(x) = m, where m is the message Alice sends on input x in the arbitrary deterministic
protocol Π").

Alice's message `msg x` is a string of exactly `c` bits; Bob's output `out m y` depends on the
message and his input. The communication cost is `c`. -/
structure DetOneWayProtocol (X Y Z : Type) (c : ℕ) where
  /-- Alice's `c`-bit message on input `x`. -/
  msg : X → (Fin c → Bool)
  /-- Bob's output on message `m` and input `y`. -/
  out : (Fin c → Bool) → Y → Z

namespace DetOneWayProtocol

variable {X Y Z : Type} {c : ℕ}

/-- The protocol is **exact** (succeeds with probability `1`) for the relation `R`: on every
input `(x, y)`, Bob's output lies in `R(x, y)`. -/
def IsExact (P : DetOneWayProtocol X Y Z c) (R : X → Y → Z → Prop) : Prop :=
  ∀ x y, R x y (P.out (P.msg x) y)

end DetOneWayProtocol

end PelagicFF.Supplement



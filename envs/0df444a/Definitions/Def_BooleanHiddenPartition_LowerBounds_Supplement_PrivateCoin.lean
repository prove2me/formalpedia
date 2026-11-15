-- Prove2me | Definitions.Def_BooleanHiddenPartition_LowerBounds_Supplement_PrivateCoin
-- name    : BooleanHiddenPartition_LowerBounds_Supplement_PrivateCoin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:13:26.507422+00:00
-- url     : https://prove2.me/theorems/b7abd1b2-3918-4dd9-acd4-8f3b524d6565
-- title:
--   Private-coin one-way protocols and acceptance probability
-- statement:
--   Let $X$ and $Y$ be Alice's and Bob's input sets, and let $c\in\mathbb N$ be the message cost in bits. A private-coin one-way protocol specifies, for each $x\in X$, a probability vector $e_x$ on $\{0,\ldots,2^c-1\}$ and, for each $y\in Y$ and message $a$, an acceptance probability $D(y,a)\in[0,1]$. Alice and Bob have independent private randomness. The YES probability is
--
--   $$P_{\mathrm{acc}}(x,y)=\sum_{a=0}^{2^c-1}e_x(a)D(y,a),\qquad \sum_a e_x(a)=1.$$
--
--   The encoder sees only Alice's input, and the decoder sees only Bob's input and the received message. There is no shared random seed. This general object is separate from the hidden-partition promise and implements the private-coin protocol obtained after the Newman step in Theorem 12.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, Characterizing Quantum Advantage for Generalizations of the Boolean Hidden Matching Problem, STOC 2027 submission #1085 (October 2026), p. 27, final paragraph of the proof of Theorem 12; p. 11, footnote 8

import Definitions.Def_BooleanHiddenPartition_LowerBounds_Scalar

open scoped BigOperators
set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds.Supplement

/-- A c-bit one-way protocol with independent private coins, on arbitrary input types.
Alice samples a message using her input alone; Bob's acceptance kernel sees only
his input and that message. There is no public random seed. -/
structure PrivateCoinProtocol (X Y : Type) (c : ℕ) where
  enc : X → Fin (2 ^ c) → ℝ
  enc_mass : ∀ x, IsMass (enc x)
  dec : Y → Fin (2 ^ c) → ℝ
  dec_range : ∀ y a, 0 ≤ dec y a ∧ dec y a ≤ 1

/-- Acceptance probability with independent Alice and Bob randomness. -/
def privateAccept {X Y : Type} {c : ℕ} (P : PrivateCoinProtocol X Y c)
    (x : X) (y : Y) : ℝ :=
  ∑ a, P.enc x a * P.dec y a

end BooleanHiddenPartition.LowerBounds.Supplement



-- Prove2me | Definitions.Def_DDNNFNeg_condFrac
-- name    : DDNNFNeg_condFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:11.417923+00:00
-- url     : https://prove2.me/theorems/2ee1df51-e197-43a1-8709-42f822e402ad
-- title:
--   Conditional probability under the uniform law on a finite set
-- statement:
--   For a finite set $I$ and predicates $P, Q$ on $I$, the conditional probability of $P$ given $Q$ for a uniformly random element of $I$ is the counting ratio
--   $$
--   \mathbb P[P \mid Q] = \frac{|\{a \in I : P(a) \wedge Q(a)\}|}{|\{a \in I : Q(a)\}|} .
--   $$
--
--   **Formalization Note** When no element of $I$ satisfies $Q$ (a conditioning event of probability $0$) the value is Lean's $x/0 = 0$. The paper conditions only on events of positive probability, and the statements using this ratio are upper bounds, which hold trivially at that value.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §5.2, pp.13–14

import Mathlib

namespace DDNNFNeg

/-- The conditional probability `P[P | Q]` for an element drawn uniformly at random from the
finite set `I` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §5.2, pp.13–14), written as the counting ratio
`|{a ∈ I : P a ∧ Q a}| / |{a ∈ I : Q a}|`.

**Formalization Note** When no element of `I` satisfies `Q` (a conditioning event of
probability zero) the value is Lean's `x / 0 = 0`; the paper conditions only on events of
positive probability, and every statement using `condFrac` is an upper bound, which is
trivially true at that junk value. -/
noncomputable def condFrac {α : Type*} (I : Finset α) (P Q : α → Prop) : ℝ := by
  classical
  exact ((I.filter (fun a => P a ∧ Q a)).card : ℝ) / ((I.filter Q).card : ℝ)

end DDNNFNeg



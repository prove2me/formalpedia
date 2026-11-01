-- Prove2me | Definitions.Def_RelaxRoundPoA_RandomBid
-- name    : RelaxRoundPoA_RandomBid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:16.387828+00:00
-- url     : https://prove2.me/theorems/5da217aa-03d7-4783-bbe3-3fe5325ed4a5
-- title:
--   Randomized deviation of one agent
-- statement:
--   A **randomized deviation** of agent $i$ is a random bid: a probability space $(A,P)$ together with a map $X:A\to\mathcal V_i$. The agent draws $a\sim P$ and bids $X(a)$.
--
--   This represents the "possibly randomized strategy" $b_i'$ of the smoothness framework.
--
--   **Formalization Note** There is no σ-algebra on a class of functions, so a mixed strategy is a random variable into the class on an arbitrary probability space (in the universe of $\Omega'$, which contains the class and every mixture over it); every mixture arises this way. Only the expected utility of the random bid is integrated, and its integrability is part of the definition of smoothness.
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §2, p.7

import Mathlib

open MeasureTheory NNReal

universe u

namespace RelaxRoundPoA

/-- **Randomized deviation of one agent.**
Dütting, Kesselheim, Tardos, arXiv:1511.09208v1, §2, p.7: in the smoothness framework each agent
`i` has a deviation `b'_i`, a "possibly randomized strategy".

A `RandomBid Val i` is a random bid of agent `i`: a probability space `(A, P)` and a map `X` from
`A` to agent `i`'s weight class `Val i`; the deviation bids `X a` with `a ∼ P`.

**Formalization Note** Mathlib carries no σ-algebra on a class of functions, so a mixed strategy
over bids is a random variable into the class, on any probability space; every mixture (finite or
not) arises this way. The sample space lives in the universe of `Ω'`, which contains the bid
class itself and every mixture over it. Measurability of `X` is not required: only the expected utility
`a ↦ u_i((X a, b_{−i}), v_i)` is integrated, and its integrability is part of `IsSmooth`. -/
structure RandomBid {N : Type*} {Ω' : Type u} (Val : N → Set (Ω' → ℝ≥0)) (i : N) where
  /-- The sample space of the randomization. -/
  A : Type u
  /-- Its σ-algebra. -/
  [measurableSpace : MeasurableSpace A]
  /-- The randomization `P`. -/
  P : Measure A
  /-- `P` is a probability measure. -/
  [isProb : IsProbabilityMeasure P]
  /-- The bid `X a` placed when the randomization is `a`. -/
  X : A → Ω' → ℝ≥0
  /-- Every realized bid lies in agent `i`'s class. -/
  mem : ∀ a, X a ∈ Val i

attribute [instance] RandomBid.measurableSpace RandomBid.isProb

end RelaxRoundPoA



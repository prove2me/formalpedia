-- Prove2me | Definitions.Def_StochasticProg_RecourseKKT_RecourseNotNegInf
-- name    : StochasticProg_RecourseKKT_RecourseNotNegInf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:47:54.973379+00:00
-- url     : https://prove2.me/theorems/de3359ff-87a7-44e8-8bd1-804a2ad5b7fa
-- title:
--   Standing assumption: $Q(x,\xi)$ is not $-\infty$
-- statement:
--   The standing assumption of §3.1c from p. 112 on: the second-stage value is not $-\infty$. Here it is required in the form
--
--   $$
--   \text{for every } x \in \mathbb R^{n_1}: \quad Q(x, \xi(\omega)) \neq -\infty \ \text{ for } P\text{-almost every } \omega .
--   $$
--
--   The book states it for every realization; the almost-sure form, chosen for each $x$ separately, is implied by it and is all that matters for $\mathcal Q$, which ignores events of probability zero (p. 110).
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1c, printed p. 112 (PDF p. 137)

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_RecourseData
import Definitions.Def_StochasticProg_RecourseKKT_secondStageValue
open MeasureTheory

namespace StochasticProg.RecourseKKT

/-- **The standing assumption "Q(x, ξ) is not −∞".**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1c, printed p. 112 (PDF p. 137): "We now turn to the properties of
Q(x, ξ), assuming it is not −∞. First, observe that Q(x, ξ) enjoys all the properties of
Theorem 2."

For every first-stage decision `x`, the second-stage value `Q(x, ξ(ω))` is different from `−∞` for
almost every `ω`.

**Formalization Note.** The book's assumption is for every realization; the Lean condition only
asks it almost surely, for each `x` separately (`∀ x, ∀ᵐ ω`), which the book's assumption implies.
Realizations of probability zero do not affect `𝒬` (p. 110). -/
def RecourseNotNegInf {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) (pb : RecourseData Ω n1 m1 n2 m2) : Prop :=
  ∀ x : Fin n1 → ℝ, ∀ᵐ ω ∂P, secondStageValue pb.W (pb.q ω) (pb.h ω) (pb.T ω) x ≠ ⊥

end StochasticProg.RecourseKKT



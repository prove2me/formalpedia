-- Prove2me | Definitions.Def_ExpConMinimax_SampleModel
-- name    : ExpConMinimax_SampleModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:19.901238+00:00
-- url     : https://prove2.me/theorems/679cc85e-e9af-4579-88b6-d6e527823b54
-- title:
--   The i.i.d. sampling model of Algorithm 1
-- statement:
--   On a probability space $(\Omega,\mathbb P)$, the sample tuples $S_t=(\omega^1_t,\omega^2_t,\xi^1_t,\xi^2_t,\zeta^1_t,\zeta^2_t)$, $t=0,1,2,\dots$, follow the **sampling model** if they are measurable, mutually independent across $t$, and each has the product law
--   $$P_\omega\otimes P_\omega\otimes P_\xi\otimes P_\xi\otimes P_\zeta\otimes P_\zeta,$$
--   that is, within an iteration the two queries of the oracle are independent realizations of $\omega,\xi,\zeta$.
--
--   This is the randomness under which the expectations of Lemma 5, Proposition 7 and Theorem 9 are taken.
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, §2, p.8 ("the SO independently returns"); §3, p.10 (two independent realizations per iteration)

import Mathlib
import Definitions.Def_ExpConMinimax_Oracle

namespace ExpConMinimax

open MeasureTheory ProbabilityTheory

/-- **The sampling model of Algorithm 1.**
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, §2, p.8 ("the SO independently returns …") and §3, p.10: "In iteration
`t`, we query the SO at `(xₜ,yₜ)` twice … Here, `{ωʲₜ, ξʲₜ, ζʲₜ}_{j=1,2}` represents two
independent realizations of random variables `ω, ξ, ζ` in iteration `t`. Consequently, the
returned stochastic function values and sub-gradients are *independent* of each other."

`SampleModel O Pr S` says that, on the probability space `(Ω, Pr)`, the per-iteration sample
tuples `S t = (ω¹ₜ, ω²ₜ, ξ¹ₜ, ξ²ₜ, ζ¹ₜ, ζ²ₜ)`, `t = 0, 1, 2, …`, are measurable and mutually
independent across iterations, and that within an iteration the six samples are independent
with laws `μω, μω, μξ, μξ, μζ, μζ`.

**Formalization Note.** Independence within an iteration is encoded by the law of `S t`
being the product measure `μω ⊗ μω ⊗ μξ ⊗ μξ ⊗ μζ ⊗ μζ`. -/
def SampleModel {dx dy m₁ m₂ : ℕ} {Sω Sξ Sζ : Type*} [MeasurableSpace Sω]
    [MeasurableSpace Sξ] [MeasurableSpace Sζ] (O : Oracle dx dy m₁ m₂ Sω Sξ Sζ)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) (S : ℕ → Ω → SampleTuple Sω Sξ Sζ) :
    Prop :=
  (∀ t, Measurable (S t)) ∧
  iIndepFun (fun t => S t) Pr ∧
  ∀ t, Pr.map (S t) = O.μω.prod (O.μω.prod (O.μξ.prod (O.μξ.prod (O.μζ.prod O.μζ))))

end ExpConMinimax



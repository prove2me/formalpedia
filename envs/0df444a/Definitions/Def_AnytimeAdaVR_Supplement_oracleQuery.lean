-- Prove2me | Definitions.Def_AnytimeAdaVR_Supplement_oracleQuery
-- name    : AnytimeAdaVR_Supplement_oracleQuery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:28:46.743904+00:00
-- url     : https://prove2.me/theorems/8d0d62a5-45ac-4821-9122-5d456c916500
-- title:
--   One counted stochastic gradient evaluation
-- statement:
--   A **counted oracle call** evaluates the stochastic gradient $g(x;\xi)$ at a point $x\in\mathbb R^d$ with a sample $\xi$ and increases a running count of gradient evaluations by one.
--
--   Algorithm 1 makes every one of its gradient evaluations through this call, including the initialization of each stage, both evaluations of a shared-sample pair in stage M, and the validation gradients. The final value of the count is therefore the number of gradient evaluations the algorithm uses, which Theorem 1 compares with the budget $T$.
--
--   **Formalization Note** The call is a computation in Lean's state monad `StateM ℕ`: it increments the state by $1$ and returns `g x ξ`.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41001434449aea8ba3a6ba5d66658a8f94ea9ffeebad36bbb903374006), §2, p.4 ("The budget includes initialization, shared-sample evaluations, and candidate validation")

import Mathlib

namespace AnytimeAdaVR.Supplement

/-- **One counted gradient evaluation.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction
across Smoothness and Noise Conditions* (preprint, 2026), §2, p.4: "The budget includes
initialization, shared-sample evaluations, and candidate validation."

`oracleQuery g x s` returns the stochastic gradient `g(x; s)` at the point `x` with the sample `s`
and increments the evaluation counter (the state, a natural number) by one.

**Formalization Note.** Every gradient evaluation of Algorithm 1
(`AnytimeAdaVR.Supplement.alg1Run`) goes through this function, so the final counter is the number
of gradient evaluations the algorithm makes, computed from its structure. -/
def oracleQuery {d : ℕ} {Ξ : Type*}
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (s : Ξ) : StateM ℕ (EuclideanSpace ℝ (Fin d)) := do
  modify (· + 1)
  pure (g x s)

end AnytimeAdaVR.Supplement



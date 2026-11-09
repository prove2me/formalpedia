-- Prove2me | Definitions.Def_HypClass1_condSucc
-- name    : HypClass1_condSucc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:17:48.914195+00:00
-- url     : https://prove2.me/theorems/95d34022-d46c-427a-9cad-e990d162c3b7
-- title:
--   Probability conditioned on the success of a randomized algorithm
-- statement:
--   A **randomized algorithm** that may fail is described by the probability distribution $\mu$ of its result, which is either a failure symbol or an output $x$. For a property $A$ of outputs, the probability of $A$ **conditioned on the event that the algorithm succeeds** is
--   $$
--   \mathbb P(A \mid \text{success}) = \frac{\mu\{x : A(x)\}}{1 - \mu(\text{failure})}.
--   $$
--   Lemmas 6.1 and 6.5 state their distributional properties in this form.
--
--   **Formalization Note** $\mu$ is a `PMF (Option α)` with `none` the failure. The paper makes no claim about running time, so only the output law matters. When the algorithm fails with probability one the quotient is $0$ in Lean; the statements exclude that case.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Lemma 6.1 (D3)–(D4) p.16, Lemma 6.5 p.21

import Mathlib

namespace HypClass1

/-- **Probability conditioned on success** for a randomized algorithm. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Lemma 6.1 (D3)–(D4)
p.16 ("Conditioned on the event that the algorithm succeeds, the probability that …"), Lemma 6.5
(E1)–(E3) p.21.

A randomized algorithm is a probability distribution `μ : PMF (Option α)` on its outputs, with
`none` standing for failure. `condSucc μ A = μ{some x : A x} / (1 − μ{none})` is the probability of
`A` for the output, conditioned on the algorithm succeeding.

**Formalization Note.** The paper claims nothing about running time, so an algorithm is just its
output law. If the algorithm fails with probability one, the quotient is `0/0 = 0` in Lean; the
statements of the mission exclude that case. -/
noncomputable def condSucc {α : Type*} (μ : PMF (Option α)) (A : α → Prop) : ℝ :=
  (μ.toOuterMeasure {o | ∃ x, o = some x ∧ A x}).toReal / (1 - (μ none).toReal)

end HypClass1



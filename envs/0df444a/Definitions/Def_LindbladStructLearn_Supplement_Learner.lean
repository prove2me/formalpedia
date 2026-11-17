-- Prove2me | Definitions.Def_LindbladStructLearn_Supplement_Learner
-- name    : LindbladStructLearn_Supplement_Learner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:42:13.417017+00:00
-- url     : https://prove2.me/theorems/e213d34f-c62c-4939-a391-b2d13b50cc5e
-- title:
--   Success probability of a general adaptive learner with ancillas
-- statement:
--   The lower bound of Section 6 holds against learning algorithms that "query the dynamics adaptively, have access to ancillary systems, and use entangled operations/measurements" (p.53). Such a learner is a public bounded-query protocol $p$ (`LindbladTolerant.Testing.Protocol`):
--
--   1. an initial state of the $n$ qubits together with a memory of any finite dimension;
--   2. a finite number of rounds, each applying $e^{t\mathcal L}\otimes\mathrm{id}$ for a duration $t\ge0$ that may depend on all earlier outcomes, followed by a quantum instrument with arbitrary measurable outcomes and outcome-dependent memory.
--
--   To this the learner adds an estimator $\mathrm{est}$ mapping the complete outcome history to a coefficient vector $\widehat\lambda$. Its **success probability** on $\mathcal L_\lambda$ is the Born probability, under the actual channels $e^{t\mathcal L_\lambda}$, that
--   $$|\widehat\lambda_{(P_1,P_2)}-\lambda_{(P_1,P_2)}|\le\varepsilon\quad\text{for every pair with }P_1\ne I.$$
--
--   This is the event of Theorem 6.1: the coefficients are learned to $\varepsilon$-error in $\infty$-norm.
--
--   **Formalization Note** The protocol's final binary effect is replaced by the projector onto the success event. The published `outputProbability` then gives its probability.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 6.1, p.53, and the access model of §6, p.53

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_protocols
import Definitions.Def_LindbladStructLearn_lindbladSuper

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal

namespace LindbladStructLearn.Supplement

open LindbladTolerant.Testing

/-- The success probability of a general learner (Lewis–Tang–Wright, *Learning the structure of open
quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 6.1, p.53, and §6,
p.53: algorithms that "query the dynamics adaptively, have access to ancillary systems, and use
entangled operations/measurements").

A learner is a public bounded-query protocol `p` (`LindbladTolerant.Testing.Protocol`: an initial state
on the system and a memory of any finite dimension, then `p.queries` rounds, each applying
`e^(t L) ⊗ id` for a duration `t ≥ 0` that may depend on all earlier outcomes followed by a quantum
instrument with arbitrary measurable outcomes) together with an estimator `est` that maps the complete
outcome history to a coefficient vector. Its success probability on the Lindbladian `L_λ` (the
published `lindbladSuper λ`) is the Born probability that the estimate is within `ε` of `λ` on every
coefficient `λ_(P₁,P₂)`, `P₁ ≠ I`: the protocol's final binary effect is replaced by the projector
onto that event, and the published `outputProbability` composes the actual channels `e^(t L_λ)`. -/
noncomputable def learnSuccess {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (p : Protocol n Ω)
    (est : List Ω → Pauli n × Pauli n → ℂ) (ε : ℝ) (lam : Pauli n × Pauli n → ℂ) : ℝ≥0∞ := by
  classical
  exact outputProbability
    { p with effect := fun h =>
        if ∀ P : Pauli n × Pauli n, P.1 ≠ 0 → ‖est h P - lam P‖ ≤ ε then 1 else 0 }
    (lindbladSuper lam) true

end LindbladStructLearn.Supplement



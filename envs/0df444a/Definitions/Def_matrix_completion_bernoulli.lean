-- Prove2me | Definitions.Def_matrix_completion_bernoulli
-- name    : matrix_completion_bernoulli
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-13T20:48:11.935406+00:00
-- url     : https://prove2.me/theorems/47499e78-f2da-4639-9bba-cbcd748bb2e4
-- statement:
--   This definition module provides the independent Bernoulli sampling model and its event-probability language.
--
--   $$
--   \Omega\sim\operatorname{Bernoulli}(p),
--   \qquad
--   \mathbb P_p(E)=\operatorname{bernoulliEventProb}(p,E).
--   $$
--
--   Module overview: Bernoulli observation model for matrix completion. The paper proves the probabilistic estimates first for independent Bernoulli sampling with inclusion probability $p = m/(n_{1}\,n_{2})$, then transfers the failure estimate to the fixed-cardinality uniform model.
--
--   Documented declarations:
--   1. Probability weight of a particular observation set in the independent Bernoulli model with inclusion probability $p$.
--   2. Bernoulli-model probability that nuclear-norm minimization uniquely recovers $M$.
--   3. Expectation of a real-valued statistic of the Bernoulli observation set.
--   4. Expectation over two independent Bernoulli observation sets with the same inclusion probability.
--   5. Bernoulli-model probability that nuclear-norm minimization uniquely recovers $M$.
--
--   Role in the mission. Key declarations include bernoulliObservationWeight, bernoulliEventProb, bernoulliExpectation, bernoulliPairExpectation, bernoulliSuccessProb. These definitions provide shared vocabulary for the Exact Matrix Completion decomposition, so theorem statements can refer to sampling models, recovery events, tangent-space geometry, and concentration estimates without restating the infrastructure each time.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_svd

/-!
Bernoulli observation model for matrix completion.

The paper proves the probabilistic estimates first for independent Bernoulli
sampling with inclusion probability `p = m / (n1 * n2)`, then transfers the
failure estimate to the fixed-cardinality uniform model.
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Probability weight of a particular observation set in the independent
Bernoulli model with inclusion probability `p`. -/
noncomputable def bernoulliObservationWeight {n1 n2 : Nat} (p : Real)
    (Omega : Finset (Fin n1 × Fin n2)) : Real :=
  p ^ Omega.card *
    (1 - p) ^ (Fintype.card (Fin n1 × Fin n2) - Omega.card)

/-- Bernoulli-model probability that nuclear-norm minimization uniquely
recovers `M`. -/
noncomputable def bernoulliEventProb {n1 n2 : Nat} (p : Real)
    (Event : Finset (Fin n1 × Fin n2) → Prop) : Real :=
  ∑ Omega : Finset (Fin n1 × Fin n2),
    if Event Omega then bernoulliObservationWeight p Omega else 0

/-- Expectation of a real-valued statistic of the Bernoulli observation set. -/
noncomputable def bernoulliExpectation {n1 n2 : Nat} (p : Real)
    (F : Finset (Fin n1 × Fin n2) → Real) : Real :=
  ∑ Omega : Finset (Fin n1 × Fin n2),
    bernoulliObservationWeight p Omega * F Omega

/-- Expectation over two independent Bernoulli observation sets with the same
inclusion probability. -/
noncomputable def bernoulliPairExpectation {n1 n2 : Nat} (p : Real)
    (F : Finset (Fin n1 × Fin n2) →
      Finset (Fin n1 × Fin n2) → Real) : Real :=
  ∑ Omega : Finset (Fin n1 × Fin n2),
    ∑ Omega' : Finset (Fin n1 × Fin n2),
      bernoulliObservationWeight p Omega *
        bernoulliObservationWeight p Omega' * F Omega Omega'

/-- Bernoulli-model probability that nuclear-norm minimization uniquely
recovers `M`. -/
noncomputable def bernoulliSuccessProb {n1 n2 : Nat} (p : Real)
    (M : RealMatrix n1 n2) : Real :=
  bernoulliEventProb p (fun Omega => IsUniqueMinimizer Omega M)

end MatrixCompletion



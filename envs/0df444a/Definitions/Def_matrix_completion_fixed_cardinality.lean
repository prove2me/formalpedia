-- Prove2me | Definitions.Def_matrix_completion_fixed_cardinality
-- name    : matrix_completion_fixed_cardinality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-06-13T22:55:25.511753+00:00
-- url     : https://prove2.me/theorems/7dc69b8d-7b0d-42c1-acf7-501d8460762d
-- statement:
--   This definition module provides fixed-cardinality event probabilities and the bridge from Bernoulli sampling back to uniform samples of exactly m entries.
--
--   $$
--   \Omega\sim \text{uniform on }\{\Omega:|\Omega|=m\},
--   \qquad
--   \mathbb P_{|\Omega|=m}(E)=\operatorname{fixedCardinalityEventProb}(m,E).
--   $$
--
--   Module overview: Generic fixed-cardinality event probabilities and binomial-cardinality weights. These are reusable probability interfaces for the Bernoulli-to-uniform transfer in Section 4.1. The matrix-completion success probability in Def_matrix_completion_basic is a specialization of fixedCardinalityEventProb.
--
--   Documented declarations:
--   1. Uniform probability of an event over all observation sets of cardinality $m$.
--   2. Binomial probability of selecting exactly $k$ elements out of $N$ under independent Bernoulli sampling with inclusion probability $p$.
--   3. Binomial lower tail up to and including $m$.
--
--   Role in the mission. Key declarations include fixedCardinalityEventProb, binomialCardinalityProb, binomialLowerTailProb. These definitions provide shared vocabulary for the Exact Matrix Completion decomposition, so theorem statements can refer to sampling models, recovery events, tangent-space geometry, and concentration estimates without restating the infrastructure each time.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_bernoulli

/-!
Generic fixed-cardinality event probabilities and binomial-cardinality weights.

These are reusable probability interfaces for the Bernoulli-to-uniform transfer
in Section 4.1.  The matrix-completion success probability in
`Def_matrix_completion_basic` is a specialization of `fixedCardinalityEventProb`.
-/

namespace MatrixCompletion

open scoped Classical BigOperators
open Finset

/-- Uniform probability of an event over all observation sets of cardinality
`m`. -/
noncomputable def fixedCardinalityEventProb {n1 n2 : Nat} (m : Nat)
    (Event : Finset (Fin n1 × Fin n2) → Prop) : Real :=
  let sampleSpace := Finset.powersetCard m (Finset.univ : Finset (Fin n1 × Fin n2))
  ((sampleSpace.filter Event).card : Real) / sampleSpace.card

/-- Binomial probability of selecting exactly `k` elements out of `N` under
independent Bernoulli sampling with inclusion probability `p`. -/
noncomputable def binomialCardinalityProb (N k : Nat) (p : Real) : Real :=
  (Nat.choose N k : Real) * p ^ k * (1 - p) ^ (N - k)

/-- Binomial lower tail up to and including `m`. -/
noncomputable def binomialLowerTailProb (N m : Nat) (p : Real) : Real :=
  ∑ k ∈ Finset.range (m + 1), binomialCardinalityProb N k p

end MatrixCompletion



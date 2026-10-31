-- Prove2me | Definitions.Def_MarkovEntanglementExact_inducedMatrix
-- name    : MarkovEntanglementExact_inducedMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:13.694986+00:00
-- url     : https://prove2.me/theorems/a1c1348b-b2eb-4247-b378-bd1846b7a396
-- title:
--   The transition matrix $P^\pi_{AB}$ on joint state-action pairs
-- statement:
--   For a two-agent MDP with kernel $P$ and policy $\pi$, the **induced transition matrix** $P^\pi_{AB}$ is indexed by joint state-action pairs, and
--   $$P^\pi_{AB}(s',a'\mid s,a)=P(s'\mid s,a)\,\pi(a'\mid s').$$
--   Here $s=(s_A,s_B)$ and $a=(a_A,a_B)$.
--
--   This matrix is the object of Definition 1, Theorem 1 and Theorem 2 of the paper: separability and the Q-values are all properties of it.
--
--   **Formalization Note** Agent $A$'s state-action pairs form the sigma type `Σ s, AA s`, and agent $B$'s `Σ s, AB s`. The matrix is indexed by the product of the two, so an index `p` carries agent $A$'s pair `p.1` and agent $B$'s pair `p.2`, which is the index shape of the published `tensorProd` and `IsSeparable`.
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §2, p.7

import Mathlib

open scoped BigOperators

namespace MarkovEntanglementExact

/-- The transition matrix `P^π_AB` of a two-agent MDP under a policy, on joint state-action
pairs: `P^π_AB(s', a' | s, a) = P(s' | s, a) · π(a' | s')`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §2, p.7.

**Formalization Note.** Agent `A`'s state-action pairs are the sigma type `Σ s, AA s`, with
`AA s` the feasible action set of footnote 1, p.8, and likewise for `B`. The matrix is indexed by
`(Σ s, AA s) × (Σ s, AB s)`, so that an entry `p` holds agent `A`'s pair `p.1` and agent `B`'s
pair `p.2`, which is the index shape of the published `tensorProd` and `IsSeparable`. -/
def inducedMatrix {SA SB : Type*} {AA : SA → Type*} {AB : SB → Type*}
    (kernel : (s : SA × SB) → AA s.1 × AB s.2 → SA × SB → ℝ)
    (π : (s : SA × SB) → AA s.1 × AB s.2 → ℝ) :
    Matrix ((Σ s, AA s) × (Σ s, AB s)) ((Σ s, AA s) × (Σ s, AB s)) ℝ :=
  fun p q =>
    kernel (p.1.1, p.2.1) (p.1.2, p.2.2) (q.1.1, q.2.1) * π (q.1.1, q.2.1) (q.1.2, q.2.2)

end MarkovEntanglementExact



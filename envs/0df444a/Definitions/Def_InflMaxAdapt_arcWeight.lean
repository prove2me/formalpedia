-- Prove2me | Definitions.Def_InflMaxAdapt_arcWeight
-- name    : InflMaxAdapt_arcWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:32:39.12925+00:00
-- url     : https://prove2.me/theorems/35246716-c4f9-4fa6-a4ab-0c50e5a88a4d
-- title:
--   Law of the live arc set $P(A = A')$
-- statement:
--   An instance of influence maximization is a finite vertex set $V$ together with a probability vector $\mathbf p \in [0,1]^{V^2}$. The random set $A \subseteq V^2$ of **live arcs** has the law
--   $$
--   \mathbb P(A = A') \;=\; \prod_{a \in A'} p_a \prod_{a \in V^2 \setminus A'} (1 - p_a), \qquad A' \subseteq V^2 ,
--   $$
--   so every potential arc $a \in V^2$ is live independently with probability $p_a$.
--
--   This is the independent cascade model on which every probability and expectation of the mission is computed.
--
--   **Formalization Note** $V^2$ is the product $V \times V$, loops included as in the paper. The constraint $\mathbf p \in [0,1]^{V^2}$ is not part of the definition; every theorem assumes it.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 1.1, printed p.2 (PDF p.3)

import Mathlib

namespace InflMaxAdapt

/-- The law of the random live arc set (Section 1.1, printed p.2 = PDF p.3, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)):
for an instance `(V, p)` and `A ⊆ V²`,
`P(A = A') = ∏_{a ∈ A'} p_a · ∏_{a ∈ V² \ A'} (1 − p_a)`, i.e. every potential arc `a ∈ V²` is live
independently with probability `p_a`.

**Formalization Note** `V²` is `V × V` (loops `(v, v)` included, as in the paper's `V²`); the live
arc set is a `Finset (V × V)`. The constraint `p ∈ [0,1]^{V²}` is not built in; every theorem
assumes it. -/
def arcWeight {V : Type} [Fintype V] [DecidableEq V] (p : V → V → ℝ) (A : Finset (V × V)) : ℝ :=
  (∏ a ∈ A, p a.1 a.2) * ∏ a ∈ Finset.univ \ A, (1 - p a.1 a.2)

end InflMaxAdapt



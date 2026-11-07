-- Prove2me | Definitions.Def_EulerSparsify_routingMat
-- name    : EulerSparsify_routingMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:35:09.18353+00:00
-- url     : https://prove2.me/theorems/c51bbc48-2c4c-4dcb-8a23-6e1e91eec79b
-- title:
--   Routing matrix $R=W^{-1}\sum_i b_iQ_i$, eq. (5.1)
-- statement:
--   For a nested ER partitioning of a graph with positive weights, the **routing matrix** is
--
--   $$R=W^{-1}\sum_{i\in[I]} b_i\,Q_i .\tag{5.1}$$
--
--   It sends a demand on an edge $f\in F_i$ to a circulation of $K_i$ through $f$, scaled on each edge $e$ by $b_i/w_e$.
--
--   **Formalization Note** $W^{-1}=\mathrm{diag}(1/w_e)$, the inverse of $W$ when all weights are positive, which every statement using $R$ assumes.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Equation (5.1), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_EulerSparsify_Qmat

namespace EulerSparsify

/-- **Routing matrix** `R = W⁻¹ Σ_{i∈[I]} b_i Q_i`, equation (5.1), p.17, PDF p.19.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), (5.1): "The routing matrix is defined using a composition of the Q_i matrices with
appropriate weight scaling: R := W⁻¹ Σ_{i∈[I]} b_i Q_i."

**Formalization Note.** `W⁻¹ = diag(1/w_e)`; it is the inverse of `W` only when every weight is
positive, which every statement using `R` assumes (the paper applies (5.1) to positive-weight
graphs). -/
noncomputable def routingMat {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : DiGraph V E) (P : NestedFamily V E) : Matrix E E ℝ :=
  Matrix.diagonal (fun e => (G.w e)⁻¹) * ∑ i, P.b G i • Qmat G P i

end EulerSparsify



-- Prove2me | Definitions.Def_EulerSparsify_Qmat
-- name    : EulerSparsify_Qmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:58.304204+00:00
-- url     : https://prove2.me/theorems/138f8286-e377-4eb3-9160-fe5cddeba4a1
-- title:
--   The projections $Q_i=P_{C(E_i)}-P_{C(E_i\setminus F_i)}$
-- statement:
--   For a nested ER partitioning $\{K_i,F_i,b_i\}_{i\in[I]}$ with $E_i=E(K_i)$, writing $P_F$ for the orthogonal projection onto $C(F)$, define
--
--   $$Q_i=P_{E_i}-P_{E_i\setminus F_i}.$$
--
--   $Q_i$ projects onto the circulations on $E_i$ that are orthogonal to the circulations avoiding $F_i$; Lemma 5.1 shows the $Q_i$ are mutually orthogonal projections.
--
--   **Formalization Note** $P_{C(F)}$ is defined from the subspace; the paper's formula $P_{C(F)}=I_F-B_FL^\dagger_{\widehat G_F}B_F^\top$ is a fact about it, not its definition.
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §5.1.1, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph_circ
import Definitions.Def_EulerSparsify_projMat
import Definitions.Def_EulerSparsify_NestedFamily

namespace EulerSparsify

/-- **The projections `Q_i = P_{E_i} − P_{E_i∖F_i}`** (§5.1.1, p.16, PDF p.18).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), §5.1.1: "For a nested ER partitioning {K_i, F_i, b_i}_{i∈[I]}, we define for each i ∈ [I]
the following orthogonal projection Q_i = P_{E_i} − P_{E_i∖F_i} where we denote E_i = E(K_i)."

Here `P_F` abbreviates `P_{C(F)}`, the orthogonal projection onto the circulation subspace
`C(F)`.

**Formalization Note.** `P_{C(F)}` is defined from the subspace (`projMat (G.circ F)`); the
paper's formula `P_{C(F)} = I_F − B_F L†_{bG_F} B_Fᵀ` is a fact about it, not its definition. -/
noncomputable def Qmat {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DiGraph V E) (P : NestedFamily V E) (i : Fin P.I) : Matrix E E ℝ :=
  projMat (G.circ (P.Ed i)) - projMat (G.circ (P.Ed i \ P.F i))

end EulerSparsify



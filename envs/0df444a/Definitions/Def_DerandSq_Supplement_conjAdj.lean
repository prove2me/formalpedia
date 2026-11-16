-- Prove2me | Definitions.Def_DerandSq_Supplement_conjAdj
-- name    : DerandSq_Supplement_conjAdj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:04:09.970822+00:00
-- url     : https://prove2.me/theorems/91ab22ea-04ab-4079-8957-5cdc91d37d2a
-- title:
--   Permutation-conjugated adjacency matrix $B = U A U^*$ (5.1)
-- statement:
--   Let $G$ be a simple graph on $[N]$ with adjacency matrix $A$, and let $U$ be the permutation matrix of $\sigma \in S_N$. The **permutation-conjugated adjacency matrix** is
--
--   $$
--   B = U A U^* ,
--   $$
--
--   the adjacency matrix of the copy of $G$ relabelled by $\sigma$. In §5 one such matrix $B_i = U_i A_i U_i^*$ is formed for each colour $i$, with independent uniform $U_i$.
--
--   **Formalization Note** $U$ is the published real permutation matrix ($e_v \mapsto e_{\sigma(v)}$), $U^* = U^{\top}$, and $A$ is Mathlib's `G.adjMatrix ℝ`.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), (5.1), p.24

import Mathlib
import Definitions.Def_DerandSq_permMat

namespace DerandSq.Supplement

/-- The permutation-conjugated adjacency matrix `B = U A U^*` of (5.1), Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.24, where `A` is
the adjacency matrix of a simple graph `G` on `V = [N]` and `U` the permutation matrix of `σ`.

**Formalization Note** `U` is the real `DerandSq.permMat σ` (orientation `e_v ↦ e_{σ v}`) and
`U^* = Uᵀ`; `A` is Mathlib's `G.adjMatrix ℝ`. -/
noncomputable def conjAdj {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (σ : Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) ℝ :=
  DerandSq.permMat σ * G.adjMatrix ℝ * (DerandSq.permMat σ).transpose

end DerandSq.Supplement



-- Prove2me | Definitions.Def_DerandSq_Supplement_permModelAdj
-- name    : DerandSq_Supplement_permModelAdj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:01:39.551258+00:00
-- url     : https://prove2.me/theorems/96fe0701-615e-48ce-af09-d08612fa1c18
-- title:
--   Permutation-model adjacency matrix $A^{\mathrm{rand}}(U) = \sum_j (U_j + U_j^*)$
-- statement:
--   Let $U = (U_1, \dots, U_r)$ be permutation matrices of size $N \times N$. The **permutation model** of a random $d$-regular graph, $d = 2r$, has adjacency matrix
--
--   $$
--   A^{\mathrm{rand}}(U) = \sum_{j=1}^{r} \bigl(U_j + U_j^*\bigr),
--   $$
--
--   where $U_j^* = U_j^{\top}$. When $U_1, \dots, U_r$ are independent uniform permutation matrices this is the random $d$-regular (multi)graph of the permutation model on which the rotating walk of Theorem 3.4 runs.
--
--   **Formalization Note** $U_j$ is the published permutation matrix $\lambda(\sigma_j)$, $e_v \mapsto e_{\sigma_j(v)}$; vertices are `Fin N`.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), §3.1, p.14; (3.10), p.17

import Mathlib
import Definitions.Def_DerandSq_permMat

namespace DerandSq.Supplement

/-- The adjacency matrix of the permutation model, `A^rand(U^N) = ∑_{j=1}^r (U_j + U_j^*)`
(Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), §3.1, p.14, and (3.10), p.17): a `d = 2r`-regular multigraph on `[N]` built from `r`
permutations.

**Formalization Note** `U_j` is the real permutation matrix `DerandSq.permMat (U j)`
(orientation `e_v ↦ e_{σ v}`), and `U_j^* = U_jᵀ`. Indices are `Fin r`, `Fin N`. -/
noncomputable def permModelAdj {r N : ℕ} (U : Fin r → Equiv.Perm (Fin N)) :
    Matrix (Fin N) (Fin N) ℝ :=
  ∑ j, (DerandSq.permMat (U j) + (DerandSq.permMat (U j)).transpose)

end DerandSq.Supplement



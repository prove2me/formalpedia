-- Prove2me | Definitions.Def_DerandSq_Supplement_rotWalk
-- name    : DerandSq_Supplement_rotWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:02:10.154837+00:00
-- url     : https://prove2.me/theorems/2ba07a1b-761f-421a-83c9-4079d5117e87
-- title:
--   Rotating walk $A_{\mathrm{rot}}(V)$ (3.1)
-- statement:
--   Let $A$ be an $N \times N$ matrix (the adjacency matrix of a graph) and $V_1, \dots, V_{k-1}$ permutation matrices (the **rotations**). The **rotating walk** of Cohen and Maor is
--
--   $$
--   A_{\mathrm{rot}}(V) = A V_1 A V_2 \cdots V_{k-1} A \cdot A V_{k-1}^* A \cdots V_2^* A V_1^* A .
--   $$
--
--   It contains $k$ copies of $A$ on each side; for $k = 1$ (no rotations) it is $A^2$. For a symmetric $A$ it equals $M M^{\top}$ with $M = A V_1 A \cdots V_{k-1} A$.
--
--   **Formalization Note** The number of rotations $k - 1$ is a parameter $m$ and the rotations are indexed by `Fin m` (0-based); $V_i^* = V_i^{\top}$ for the real permutation matrix $V_i$.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), (3.1), p.13

import Mathlib
import Definitions.Def_DerandSq_permMat

namespace DerandSq.Supplement

/-- The rotating walk (3.1) of Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), p.13 (Cohen–Maor):
`A_rot(V) = A V_1 A V_2 ⋯ V_{k−1} A · A V_{k−1}^* A ⋯ V_2^* A V_1^* A`, for an `N × N` matrix
`A` and rotation permutations `V_1, …, V_{k−1}`.

**Formalization Note** The number of rotations `k − 1` is the parameter `m` (`V : Fin m → _`,
`V i` is `V_{i+1}`); `V_i` is the real permutation matrix `DerandSq.permMat (V i)` and
`V_i^* = V_iᵀ`. The first factor is `A · ∏_{i} (V_i A)` in increasing order, the second
`∏_{i} (A V_{k−1−i}ᵀ) · A`, i.e. the indices decrease. For `m = 0` (`k = 1`) this is `A · A`. -/
noncomputable def rotWalk {N m : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (V : Fin m → Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) ℝ :=
  (A * (List.ofFn fun i : Fin m => DerandSq.permMat (V i) * A).prod) *
    ((List.ofFn fun i : Fin m => A * (DerandSq.permMat (V (Fin.rev i))).transpose).prod * A)

end DerandSq.Supplement



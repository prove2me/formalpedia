-- Prove2me | Definitions.Def_MaxCompForest_Supplement_principalDet
-- name    : MaxCompForest_Supplement_principalDet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:15:38.035854+00:00
-- url     : https://prove2.me/theorems/1e2eb867-6a05-4fc4-9b5a-35d66ccf7a02
-- title:
--   Principal minor $\det K_F$
-- statement:
--   For a square matrix $K\in\mathbb R^{m\times m}$ and an index set $F\subseteq[m]$, the **principal minor** $\det K_F$ is the determinant of the submatrix of $K$ with rows and columns in $F$. The empty minor is $1$. For the transfer-current kernel of a graph, $\det K_F$ is the probability that a weighted random spanning tree contains the edge set $F$ (4.5).
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem 4.2, p.26 (PDF p.28)

import Mathlib
set_option autoImplicit false

namespace MaxCompForest.Supplement

variable {m : ℕ}

/-- **The principal minor** `det K_F` of a square matrix on an index set `F`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem 4.2, p.26. The empty minor is `1`. -/
noncomputable def principalDet (K : Matrix (Fin m) (Fin m) ℝ) (F : Finset (Fin m)) : ℝ :=
  (K.submatrix (fun i : F => (i : Fin m)) (fun i : F => (i : Fin m))).det

end MaxCompForest.Supplement



-- Prove2me | Definitions.Def_DerandSq_chi
-- name    : DerandSq_chi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:53:11.84879+00:00
-- url     : https://prove2.me/theorems/f9b2dd0d-34bc-4d19-bd7f-203c789e6143
-- title:
--   Characteristic polynomial $\chi_x(H)$
-- statement:
--   For a graph $H$ on $[d]$ with adjacency matrix $A_H$, $\chi_x(H) = \det(x I - A_H)$ is the **characteristic polynomial** of $A_H$, a monic real polynomial of degree $d$. For example $\chi_x(K_3) = (x - 2)(x + 1)^2$.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), below (4.3), p.19

import Mathlib

namespace DerandSq

/-- `χ_x(H)`: the characteristic polynomial `det(xI − A_H)` of the adjacency matrix `A_H` of a
graph `H` on `[d]` (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), below (4.3), p.19). -/
noncomputable def chi {d : ℕ} (H : SimpleGraph (Fin d)) : Polynomial ℝ := by
  classical exact (H.adjMatrix ℝ).charpoly

end DerandSq



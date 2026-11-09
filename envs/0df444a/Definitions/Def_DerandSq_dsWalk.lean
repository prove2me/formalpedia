-- Prove2me | Definitions.Def_DerandSq_dsWalk
-- name    : DerandSq_dsWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:55:55.041182+00:00
-- url     : https://prove2.me/theorems/43f59c61-3fba-423f-a3b0-4c5fb8aabf98
-- title:
--   Random walk matrix $M_S = A_S/(dk)$
-- statement:
--   For the derandomized square $S = G \circledS H$ of the $d$-regular graph $G$ labelled by $\pi_1, \dots, \pi_d$ via a $k$-regular graph $H$ on $[d]$, the **random walk matrix** is the normalized adjacency matrix
--   $$
--   M_S = \frac{1}{dk} A_S .
--   $$
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), §4.1, p.20

import Mathlib
import Definitions.Def_DerandSq_dsAdj

namespace DerandSq

/-- The random walk matrix `M_S = A_S / (dk)` of the derandomized square `S = G Ⓢ H` of the
`d`-regular graph `G` labelled by `π_1, …, π_d` via the `k`-regular graph `H` (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), §4.1,
p.20). -/
noncomputable def dsWalk {N d : ℕ} (π : Fin d → Equiv.Perm (Fin N)) (H : SimpleGraph (Fin d))
    (k : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  ((d : ℝ) * k)⁻¹ • dsAdj π H

end DerandSq



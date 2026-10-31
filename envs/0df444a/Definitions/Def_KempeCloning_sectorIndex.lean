-- Prove2me | Definitions.Def_KempeCloning_sectorIndex
-- name    : KempeCloning_sectorIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:23:24.310818+00:00
-- url     : https://prove2.me/theorems/be97ce95-4ae0-400e-a513-2157c71f845b
-- title:
--   The sector states $|(m+j), i, i, j, (N-i-j)\rangle$ (15)
-- statement:
--   For $m, N\in\mathbb N$ and a label $(i,j)$ with $i+j\le N$, $\mathrm{sectorIndex}_{m,N}(i,j)$ is the Fock index of the state (15)
--
--   $$|(m+j)_{a_1}, i_{a_2}, i_{b_1}, j_{b_2}, (N-i-j)_c\rangle .$$
--
--   The map is injective, and its image is the set of number states with $n_{a_1} - n_{b_2} = m$, $n_{a_2} = n_{b_1}$ and $n_{b_1} + n_{b_2} + n_c = N$, the quantities conserved by (14) starting from (13).
--
--   **Formalization Note** Defined from (15), not from the states (19).
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II B, (15), p.4

import Definitions.Def_KempeCloning_occ
import Definitions.Def_KempeCloning_Sector

namespace KempeCloning

/-- **The Fock basis states (15) of the sector.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II B, (15), p.4:
`|(m + j)_{a1}, i_{a2}, i_{b1}, j_{b2}, (N − i − j)_c⟩`.

`sectorIndex m N (i, j)` is the Fock index with occupations `m + j, i, i, j, N − i − j` in modes
`a1, a2, b1, b2, c`. It is injective, and its image is the set of Fock indices with
`n_{a1} − n_{b2} = m`, `n_{a2} = n_{b1}` and `n_{b1} + n_{b2} + n_c = N`.

**Formalization Note.** Defined from (15), not from the states (19). The subtraction `N − i − j`
is exact on `Sector N`. -/
def sectorIndex (m N : ℕ) (q : Sector N) : FockIndex :=
  occ (m + q.1.2.val) q.1.1.val q.1.1.val q.1.2.val (N - q.1.1.val - q.1.2.val)

end KempeCloning



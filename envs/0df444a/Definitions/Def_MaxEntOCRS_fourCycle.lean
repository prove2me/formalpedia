-- Prove2me | Definitions.Def_MaxEntOCRS_fourCycle
-- name    : MaxEntOCRS_fourCycle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:38.940047+00:00
-- url     : https://prove2.me/theorems/05163fec-7cdf-40ad-bf86-5cfdcceafc38
-- title:
--   The four-cycle $u, y_1, v, y_2$
-- statement:
--   The four-cycle with vertices $0 = u$, $1 = y_1$, $2 = v$, $3 = y_2$ and edges $uy_1$, $y_1v$, $vy_2$, $y_2u$. Its diagonals are $\{u, v\} = \{0, 2\}$ and $\{y_1, y_2\} = \{1, 3\}$. With all activities equal to $\alpha$, it is the equality case of Theorem 2 and the obstruction showing that $\alpha$ is the best constant for the template.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Theorem 2, p.2; Section 6, Tightness, p.8

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace MaxEntOCRS

/-- The four-cycle `u, y₁, v, y₂` of Theorem 2's equality case (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), Theorem 2, p.2, and §6
"Tightness", p.8): vertices `0 = u`, `1 = y₁`, `2 = v`, `3 = y₂` and edges
`0 = uy₁`, `1 = y₁v`, `2 = vy₂`, `3 = y₂u`. The diagonals are `{0, 2}` and `{1, 3}`. -/
def fourCycle : EdmondsMatching65.Polyhedron.Graph (Fin 4) (Fin 4) where
  ends := ![s(0, 1), s(1, 2), s(2, 3), s(3, 0)]
  loopless := by decide

end MaxEntOCRS



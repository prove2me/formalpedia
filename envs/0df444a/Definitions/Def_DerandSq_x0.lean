-- Prove2me | Definitions.Def_DerandSq_x0
-- name    : DerandSq_x0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:00:25.708383+00:00
-- url     : https://prove2.me/theorems/e6202546-cd0e-4148-9c2b-c611674b61f1
-- title:
--   $x_0$: the largest root of (4.4)
-- statement:
--   For $d \geq 3$ and a graph $H$ on $[d]$, $x_0 = x_0(d, H)$ is the **largest real root** of
--   $$
--   (d - 1)\,\chi_x(H)\,\chi''_x(H) = (d - 2)\,\chi'_x(H)^2 .
--   $$
--   For $H = K_3$, $x_0 = 3$.
--
--   **Formalization Note** Encoded as the supremum of the set of real roots of $R_{d,H}$ (`rootPoly`). That set is finite (the polynomial has leading coefficient $d \neq 0$) and, for $d \geq 3$, nonempty (it contains a root above the largest eigenvalue of $H$), so the supremum is the largest root.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), (4.4), p.19

import Mathlib
import Definitions.Def_DerandSq_rootPoly

namespace DerandSq

/-- `x₀`, the largest root of `(d − 1)·χ_x(H)·χ''_x(H) = (d − 2)·χ'_x(H)²` (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), (4.4), p.19).

**Formalization Note** Encoded as the supremum of the set of real roots of `rootPoly d H`. For
`d ≥ 3` the polynomial has leading coefficient `d ≠ 0`, so the root set is finite, and it is
nonempty (it has a root above the largest eigenvalue of `H`); the supremum is then the largest
root. -/
noncomputable def x0 (d : ℕ) (H : SimpleGraph (Fin d)) : ℝ :=
  sSup {x : ℝ | (rootPoly d H).eval x = 0}

end DerandSq



-- Prove2me | Definitions.Def_ConstrSOSP_boxA
-- name    : ConstrSOSP_boxA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:23.852371+00:00
-- url     : https://prove2.me/theorems/06b8e7db-adfd-4a35-83a4-385f762a2460
-- title:
--   Constraint matrix of the unit square
-- statement:
--   The unit square $[0,1]^2$ is $\{x: Ax\le b\}$ with
--   $$
--   A=\begin{pmatrix}I\\-I\end{pmatrix}=\begin{pmatrix}1&0\\0&1\\-1&0\\0&-1\end{pmatrix}.
--   $$
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Theorem 5.1, p.22

import Mathlib

namespace ConstrSOSP

/-- **Constraint matrix of the unit square** `[0, 1]²` (arXiv:2604.02285, 2 Nov 2026, Theorem 5.1,
p.22: "the domain is fixed to [0, 1]^2"): the rows `(1, 0)`, `(0, 1)`, `(−1, 0)`, `(0, −1)`, i.e.
`A = [I; −I]`. With `boxB = (1, 1, 0, 0)` the polytope `{Ax ≤ b}` is `[0, 1]²`. -/
def boxA : Fin 4 → Fin 2 → ℝ :=
  ![![1, 0], ![0, 1], ![-1, 0], ![0, -1]]

end ConstrSOSP



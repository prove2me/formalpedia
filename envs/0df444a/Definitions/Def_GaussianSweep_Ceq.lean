-- Prove2me | Definitions.Def_GaussianSweep_Ceq
-- name    : GaussianSweep_Ceq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:07.28493+00:00
-- url     : https://prove2.me/theorems/9e44e98c-3c17-4370-b282-bc38314a99a9
-- title:
--   Equilateral correlation matrix $C_{\mathrm{eq}}$
-- statement:
--   $C_{\mathrm{eq}}$ is the $3 \times 3$ correlation matrix of the regular simplex vector $U^*$: unit diagonal and all off-diagonal entries $-\tfrac12$.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 8.4, p.52 (PDF p.54)

import Mathlib

namespace GaussianSweep

/-- The correlation matrix `C_eq` of the regular simplex vector `U*` in three variables: unit
diagonal and all off-diagonal entries `−1/2` (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Section 8.4, p.52 (PDF p.54)). -/
noncomputable def Ceq : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if i = j then 1 else -1 / 2

end GaussianSweep



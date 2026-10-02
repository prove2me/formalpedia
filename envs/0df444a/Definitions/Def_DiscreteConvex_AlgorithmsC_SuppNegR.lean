-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_SuppNegR
-- name    : DiscreteConvex_AlgorithmsC_SuppNegR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:19:16.480988+00:00
-- url     : https://prove2.me/theorems/596806cb-6183-4e18-892c-0e17d7b939d3
-- title:
--   Negative support, real-vector version
-- statement:
--   The negative support $\operatorname{supp}^-(x-y)=\{v : x(v)<y(v)\}$, real-vector version.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §10.3.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §10.3

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The negative support of `x - y`, real-vector version. -/
noncomputable def SuppNegR (x y : V → ℝ) : Finset V := Finset.univ.filter (fun v => x v < y v)

end DiscreteConvex.AlgorithmsC



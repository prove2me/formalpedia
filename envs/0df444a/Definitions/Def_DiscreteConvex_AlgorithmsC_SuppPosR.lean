-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_SuppPosR
-- name    : DiscreteConvex_AlgorithmsC_SuppPosR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:19:10.146796+00:00
-- url     : https://prove2.me/theorems/d5cf484d-dee2-4490-8ed0-f3c5de5852eb
-- title:
--   Positive support, real-vector version
-- statement:
--   The positive support $\operatorname{supp}^+(x-y)=\{v : y(v)<x(v)\}$, real-vector version.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §10.3.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §10.3

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The positive support of `x - y`, real-vector version. -/
noncomputable def SuppPosR (x y : V → ℝ) : Finset V := Finset.univ.filter (fun v => y v < x v)

end DiscreteConvex.AlgorithmsC



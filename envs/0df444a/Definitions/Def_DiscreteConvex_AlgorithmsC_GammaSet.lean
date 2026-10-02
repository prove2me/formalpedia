-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_GammaSet
-- name    : DiscreteConvex_AlgorithmsC_GammaSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:17:28.555096+00:00
-- url     : https://prove2.me/theorems/3e69f5da-5c58-403e-af2b-86935b1d0176
-- title:
--   GammaSet
-- statement:
--   $\Gamma(Y)=\bigcup_{u\in Y}\Gamma(u)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, redeclared

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `Γ(Y) = ⋃_{u∈Y} Γ(u)`. -/
def GammaSet {U : Type*} [DecidableEq U] (Gamma : U → Finset V) (Y : Finset U) : Finset V :=
  Y.biUnion Gamma

end DiscreteConvex.AlgorithmsC



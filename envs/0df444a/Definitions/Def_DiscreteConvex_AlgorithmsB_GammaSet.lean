-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsB_GammaSet
-- name    : DiscreteConvex_AlgorithmsB_GammaSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:51:20.612684+00:00
-- url     : https://prove2.me/theorems/9a3a3a47-d731-46e2-b672-6ba66a5aa1c9
-- title:
--   GammaSet
-- statement:
--   $\Gamma(Y)=\bigcup_{u\in Y}\Gamma(u)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, preceding Eq. (10.26).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.301, preceding Eq. (10.26)

import Mathlib

namespace DiscreteConvex.AlgorithmsB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `Γ(Y) = ⋃_{u∈Y} Γ(u)`. -/
def GammaSet {U : Type*} [DecidableEq U] (Gamma : U → Finset V) (Y : Finset U) : Finset V :=
  Y.biUnion Gamma

end DiscreteConvex.AlgorithmsB



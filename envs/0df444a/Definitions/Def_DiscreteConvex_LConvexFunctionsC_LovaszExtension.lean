-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsC_LovaszExtension
-- name    : DiscreteConvex_LConvexFunctionsC_LovaszExtension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:38:29.302096+00:00
-- url     : https://prove2.me/theorems/d42c2f85-ae00-4c5a-bf94-826e722b0462
-- title:
--   LovaszExtension
-- statement:
--   The Lov\'asz extension $\hat\rho:\mathbb R^V\to\mathbb R\cup\{\pm\infty\}$ of a set function $\rho$, Eq. (4.6).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Eq. (4.6).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Eq. (4.6)

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_PosScalarMul
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SortedValues
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_ThresholdSet

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The Lovász extension `ρ̂ : Rⱽ → R∪{±∞}` of a set function `ρ`, Eq. (4.6). -/
noncomputable def LovaszExtension (rho : Finset V → WithTop ℝ) (p : V → ℝ) : WithTop ℝ :=
  let vals := SortedValues p
  let m := vals.length
  (∑ i ∈ Finset.range (m - 1),
      PosScalarMul (vals.getD i 0 - vals.getD (i + 1) 0) (rho (ThresholdSet p (i + 1)))) +
    PosScalarMul (vals.getD (m - 1) 0) (rho (ThresholdSet p m))

end DiscreteConvex.LConvexFunctionsC



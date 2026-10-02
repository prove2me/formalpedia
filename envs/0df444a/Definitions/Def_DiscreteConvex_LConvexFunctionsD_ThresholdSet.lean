-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctionsD_ThresholdSet
-- name    : DiscreteConvex_LConvexFunctionsD_ThresholdSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:02:06.715851+00:00
-- url     : https://prove2.me/theorems/232c4954-5726-461b-ab0e-29609dbe7a1f
-- title:
--   ThresholdSet
-- statement:
--   The $i$-th threshold set $U_i=\{v\in V:p(v)\ge\hat p_i\}$ (1-indexed).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Eq. (4.4).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Eq. (4.4)

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_SortedValues

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `i`-th threshold set `Uᵢ = {v ∈ V : p(v) ≥ p̂ᵢ}` (1-indexed). -/
noncomputable def ThresholdSet (p : V → ℝ) (i : ℕ) : Finset V :=
  Finset.univ.filter (fun v => (SortedValues p).getD (i - 1) 0 ≤ p v)

end DiscreteConvex.LConvexFunctionsD



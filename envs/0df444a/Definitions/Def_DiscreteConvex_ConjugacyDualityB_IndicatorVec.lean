-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_IndicatorVec
-- name    : DiscreteConvex_ConjugacyDualityB_IndicatorVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:26:23.25249+00:00
-- url     : https://prove2.me/theorems/a4e4ab26-5001-434d-bccc-3b3e412c6742
-- title:
--   IndicatorVec
-- statement:
--   The characteristic vector $\chi_Y \in \mathbb Z^V$ of $Y \subseteq V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The characteristic vector `χ_Y ∈ Zⱽ` of `Y ⊆ V`. -/
def IndicatorVec (Y : Finset V) : V → ℤ := fun v => if v ∈ Y then 1 else 0

end DiscreteConvex.ConjugacyDualityB



-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_IndicatorVec
-- name    : DiscreteConvex_ConjugacyDualityD_IndicatorVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:55:25.437256+00:00
-- url     : https://prove2.me/theorems/1e10637f-0dea-4c17-ab91-bc6e72aede52
-- title:
--   IndicatorVec
-- statement:
--   The characteristic vector $\chi_Y \in \mathbb Z^V$ of $Y \subseteq V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.133, redeclared

import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The characteristic vector `χ_Y ∈ Zⱽ` of `Y ⊆ V`. -/
def IndicatorVec (Y : Finset V) : V → ℤ := fun v => if v ∈ Y then 1 else 0

end DiscreteConvex.ConjugacyDualityD



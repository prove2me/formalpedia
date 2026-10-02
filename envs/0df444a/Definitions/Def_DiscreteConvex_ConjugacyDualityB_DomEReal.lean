-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomEReal
-- name    : DiscreteConvex_ConjugacyDualityB_DomEReal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:57.317059+00:00
-- url     : https://prove2.me/theorems/9b61661d-e82f-4906-93e3-d1e8bda366df
-- title:
--   DomEReal
-- statement:
--   The effective domain of an `EReal`-valued convex function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of an `EReal`-valued convex function. -/
def DomEReal (F : (V → ℝ) → EReal) : Set (V → ℝ) := {p | F p ≠ ⊤}

end DiscreteConvex.ConjugacyDualityB



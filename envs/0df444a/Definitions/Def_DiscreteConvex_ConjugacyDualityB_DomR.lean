-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomR
-- name    : DiscreteConvex_ConjugacyDualityB_DomR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:29.691928+00:00
-- url     : https://prove2.me/theorems/5830a02f-a309-472a-ac8f-10e741320cb4
-- title:
--   DomR
-- statement:
--   The effective domain of a real-valued function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, real-variable analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, real-variable analogue

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of a real-valued function. -/
def DomR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {p | g p ≠ ⊤}

end DiscreteConvex.ConjugacyDualityB



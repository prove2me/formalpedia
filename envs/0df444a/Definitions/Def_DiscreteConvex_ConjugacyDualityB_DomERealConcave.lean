-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomERealConcave
-- name    : DiscreteConvex_ConjugacyDualityB_DomERealConcave
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:56.2444+00:00
-- url     : https://prove2.me/theorems/175720e7-21e4-4208-917e-b168bc861e56
-- title:
--   DomERealConcave
-- statement:
--   The effective domain of an `EReal`-valued concave function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, supporting several results

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The effective domain of an `EReal`-valued concave function. -/
def DomERealConcave (F : (V → ℝ) → EReal) : Set (V → ℝ) := {p | F p ≠ ⊥}

end DiscreteConvex.ConjugacyDualityB



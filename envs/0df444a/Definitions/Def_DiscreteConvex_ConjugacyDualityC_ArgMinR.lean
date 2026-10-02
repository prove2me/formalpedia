-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_ArgMinR
-- name    : DiscreteConvex_ConjugacyDualityC_ArgMinR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:41:19.706415+00:00
-- url     : https://prove2.me/theorems/5a9b6494-0d4c-44c8-9d26-7a47a1fe3066
-- title:
--   ArgMinR
-- statement:
--   The minimizer set of a real-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion

import Mathlib

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The minimizer set of a real-domain function. -/
def ArgMinR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {p | ∀ q, g p ≤ g q}

end DiscreteConvex.ConjugacyDualityC



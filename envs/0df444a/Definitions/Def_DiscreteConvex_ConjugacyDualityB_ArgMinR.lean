-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_ArgMinR
-- name    : DiscreteConvex_ConjugacyDualityB_ArgMinR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:28:01.13302+00:00
-- url     : https://prove2.me/theorems/9ec82091-46b3-4fac-8888-c3c280e1c5a1
-- title:
--   ArgMinR
-- statement:
--   The minimizer set of a real-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, standard notion

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The minimizer set of a real-domain function. -/
def ArgMinR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {p | ∀ q, g p ≤ g q}

end DiscreteConvex.ConjugacyDualityB



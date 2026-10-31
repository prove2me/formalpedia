-- Prove2me | Definitions.Def_CombOpt_Circulation_IsIntegralVector
-- name    : CombOpt_Circulation_IsIntegralVector
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:20.774855+00:00
-- url     : https://prove2.me/theorems/f3da394a-3fe0-431a-a2c2-e1039d708317
-- title:
--   Integral real vectors
-- statement:
--   A real vector is **integral** if each of its components is an integer. It is used for flows, circulations, demand vectors and finite capacities.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), (3.3), p. 38 (PDF p. 47)

import Mathlib

namespace CombOpt.Circulation

/-- An integral real vector `x ∈ ℝ^I`: every component is an integer, as in (3.3), p. 38
(PDF p. 47), of Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998). -/
def IsIntegralVector {I : Type*} (x : I → ℝ) : Prop :=
  ∀ i, ∃ n : ℤ, x i = n

end CombOpt.Circulation



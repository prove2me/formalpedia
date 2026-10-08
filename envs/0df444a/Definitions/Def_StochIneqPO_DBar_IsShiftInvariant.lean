-- Prove2me | Definitions.Def_StochIneqPO_DBar_IsShiftInvariant
-- name    : StochIneqPO_DBar_IsShiftInvariant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:23.090144+00:00
-- url     : https://prove2.me/theorems/fa9dae04-01c4-401a-92f3-fe53359963a7
-- title:
--   Sec. 8, p. 910 — stationary path laws 𝒮_T
-- statement:
--   The class $\mathcal S_T$ consists of probability measures $P$ on the two-sided path space $E^{\mathbb Z}$ that are invariant under the shift $T$:
--
--   $$P\circ T^{-1}=P.$$
--
--   These are the distributions of stationary processes used in Theorems 7 and 8.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Sec. 7, p. 909 and Sec. 8, p. 910 (PDF pp. 11–12)

import Mathlib
import Definitions.Def_StochIneqPO_DBar_shift

namespace StochIneqPO.DBar

open MeasureTheory

/-- The class `𝒮_T` of shift-invariant probability laws on two-sided paths. -/
def IsShiftInvariant {E : Type*} [MeasurableSpace E]
    (P : Measure (ℤ → E)) : Prop :=
  IsProbabilityMeasure P ∧ P.map (shift (E := E)) = P

end StochIneqPO.DBar



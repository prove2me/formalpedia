-- Prove2me | Definitions.Def_StochIneqPO_DBar_IsPairShiftInvariant
-- name    : StochIneqPO_DBar_IsPairShiftInvariant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:37.390299+00:00
-- url     : https://prove2.me/theorems/a3f00cc6-197e-4be5-b885-2ccf88178640
-- title:
--   Sec. 8, p. 910 — stationary joint laws 𝒮_S
-- statement:
--   Let $S$ shift both coordinates of a pair of two-sided paths: $S(\omega_1,\omega_2)=(T\omega_1,T\omega_2)$. The class $\mathcal S_S$ consists of probability measures $\nu$ on $E^{\mathbb Z}\times E^{\mathbb Z}$ satisfying
--
--   $$\nu\circ S^{-1}=\nu.$$
--
--   Its elements are the stationary joint laws over which Ornstein's distance is minimized.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Sec. 8, p. 910 (PDF p. 12)

import Mathlib
import Definitions.Def_StochIneqPO_DBar_shift

namespace StochIneqPO.DBar

open MeasureTheory

/-- The class `𝒮_S` of probability laws invariant under shifting both paths. -/
def IsPairShiftInvariant {E : Type*} [MeasurableSpace E]
    (ν : Measure ((ℤ → E) × (ℤ → E))) : Prop :=
  IsProbabilityMeasure ν ∧
    ν.map (Prod.map (shift (E := E)) (shift (E := E))) = ν

end StochIneqPO.DBar



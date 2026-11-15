-- Prove2me | Definitions.Def_Kyprianou_Ch02_IndependentComponents
-- name    : Kyprianou_Ch02_IndependentComponents
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T10:12:58.990589+00:00
-- url     : https://prove2.me/theorems/d071a770-64c6-40f3-87eb-0f78c6a62aa8
-- title:
--   Mutual independence of the full Lévy–Itô component paths
-- statement:
--   Defines independence of three entire random functions of nonnegative time. This is stronger than pairwise fixed-time independence.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1, pp. 35–36; construction and components in §§2.1–2.5.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou

/-- Independence of three entire paths, not merely pairwise independence
    of their values at any fixed time. -/
def IndependentLevyItoComponents
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ) : Prop :=
  ProbabilityTheory.iIndepFun
    (fun (i : Fin 3) (ω : Ω) => fun t : ℝ≥0 =>
      if i = 0 then Xgauss t ω else
      if i = 1 then Xlarge t ω else Xsmall t ω) P

end Kyprianou



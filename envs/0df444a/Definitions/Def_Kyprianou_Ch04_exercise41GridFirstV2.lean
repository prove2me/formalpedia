-- Prove2me | Definitions.Def_Kyprianou_Ch04_exercise41GridFirstV2
-- name    : Kyprianou_Ch04_exercise41GridFirstV2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-26T07:31:59.050612+00:00
-- url     : https://prove2.me/theorems/124b1407-bc26-4069-a4a4-78628732abeb
-- title:
--   Finite capped first observation selector
-- statement:
--   Select the first successful observation in a finite grid or a deterministic default.
-- source:
--   Kyprianou (2006), Chapter 4, Exercises 4.1 and 4.9.

import Mathlib

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace Kyprianou.Ch04

/-- Finite first-hit selector with a deterministic default. -/
noncomputable def exercise41GridFirstV2 {Ω : Type}
    (D : Finset NNReal) (C : NNReal → Set Ω)
    (b : NNReal) (ω : Ω) : NNReal := by
  classical
  let H := D.filter (fun t => ω ∈ C t)
  exact if h : H.Nonempty then H.min' h else b

end Kyprianou.Ch04



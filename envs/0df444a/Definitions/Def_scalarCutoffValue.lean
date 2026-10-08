-- Prove2me | Definitions.Def_scalarCutoffValue
-- name    : scalarCutoffValue
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T10:02:21.797911+00:00
-- url     : https://prove2.me/theorems/10f67881-63ca-48cf-a1d6-ef3f95c2e03c
-- title:
--   scalarCutoffValue
-- statement:
--   Automatically extracted helper definition scalarCutoffValue from oversized parent candidate c112f3e7789a9063f38d61248d17138250d381354e7c0c9e1107ab3f08608164.
-- source:
--   candidate-decomposition:85c1bbfd-5b9a-4c0f-806f-38b7a4fe9aa5:c112f3e7789a9063f38d61248d17138250d381354e7c0c9e1107ab3f08608164

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_scalarClip
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

def scalarCutoffValue (g : ℝ → ℝ) (fare p x s : ℝ) : ℝ :=
  fare * scalarClip p x s + g (s - scalarClip p x s)



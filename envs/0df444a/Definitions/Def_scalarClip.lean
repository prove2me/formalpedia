-- Prove2me | Definitions.Def_scalarClip
-- name    : scalarClip
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T04:15:45.615482+00:00
-- url     : https://prove2.me/theorems/39f8a6e1-9c98-4d04-a075-b1786299b4ba
-- title:
--   scalarClip
-- statement:
--   Automatically extracted helper definition scalarClip from oversized parent candidate c112f3e7789a9063f38d61248d17138250d381354e7c0c9e1107ab3f08608164.
-- source:
--   candidate-decomposition:85c1bbfd-5b9a-4c0f-806f-38b7a4fe9aa5:c112f3e7789a9063f38d61248d17138250d381354e7c0c9e1107ab3f08608164

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory
open NestedSeatAlloc.IntPolicy

def scalarClip (p x s : ℝ) : ℝ := min x (max 0 (s - p))



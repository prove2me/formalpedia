-- Prove2me | Definitions.Def_Tablet_CurrentChordEstimate
-- name    : Tablet_CurrentChordEstimate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:50:58.245746+00:00
-- url     : https://prove2.me/theorems/1b4d68f9-cb8a-5dd0-a87d-25323908a875
-- title:
--   Current Chord Estimate
-- statement:
--   Definitions and structural lemmas for Current Chord Estimate, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurrentChordEstimate.lean

import Definitions.Def_Tablet_CurveCurrentBound
import Theorems.Thm_CurveCurrentBound

set_option autoImplicit false
open MeasureTheory intervalIntegral



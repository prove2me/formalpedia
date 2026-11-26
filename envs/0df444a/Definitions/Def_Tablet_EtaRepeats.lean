-- Prove2me | Definitions.Def_Tablet_EtaRepeats
-- name    : Tablet_EtaRepeats
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:56:20.942801+00:00
-- url     : https://prove2.me/theorems/738ca883-3528-416f-8b17-8d2fa1886302
-- title:
--   Eta Repeats
-- statement:
--   Definitions and structural lemmas for Eta Repeats, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/EtaRepeats.lean

import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_CurveLenMeasurable
import Definitions.Def_Tablet_CurveRestrictTotAgrees
import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Definitions.Def_Tablet_CurveRestrictTotMeasurable
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_PsiReindex
import Definitions.Def_Tablet_PsiMeasurable
import Theorems.Thm_CurveLenMeasurable
import Theorems.Thm_CurveRestrictTotAgrees
import Theorems.Thm_CurveRestrictTotMeasurable
import Theorems.Thm_CurveScaledEvalMeasurable
import Theorems.Thm_PsiMeasurable
import Theorems.Thm_PsiReindex

set_option autoImplicit false
open MeasureTheory



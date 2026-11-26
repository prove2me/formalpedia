-- Prove2me | Definitions.Def_Tablet_EtaRepeatsTilde
-- name    : Tablet_EtaRepeatsTilde
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:59:23.938483+00:00
-- url     : https://prove2.me/theorems/d163f51b-eb0b-52f2-963d-fc2c8a233b59
-- title:
--   Eta Repeats Tilde
-- statement:
--   Definitions and structural lemmas for Eta Repeats Tilde, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/EtaRepeatsTilde.lean

import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_CurveLenMeasurable
import Definitions.Def_Tablet_CurveRestrictTotAgrees
import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Definitions.Def_Tablet_CurveRestrictTotMeasurable
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_EtaRepeats
import Definitions.Def_Tablet_PsiReindex
import Definitions.Def_Tablet_PsiReindexTilde
import Definitions.Def_Tablet_PsiTildeMeasurable
import Theorems.Thm_CurveLenMeasurable
import Theorems.Thm_CurveRestrictTotAgrees
import Theorems.Thm_CurveRestrictTotMeasurable
import Theorems.Thm_CurveScaledEvalMeasurable
import Theorems.Thm_EtaRepeats
import Theorems.Thm_PsiReindex
import Theorems.Thm_PsiReindexTilde
import Theorems.Thm_PsiTildeMeasurable

set_option autoImplicit false
open MeasureTheory



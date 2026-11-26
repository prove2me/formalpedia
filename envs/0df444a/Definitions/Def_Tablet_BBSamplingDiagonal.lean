-- Prove2me | Definitions.Def_Tablet_BBSamplingDiagonal
-- name    : Tablet_BBSamplingDiagonal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:03:20.157009+00:00
-- url     : https://prove2.me/theorems/3dd7ac9b-8e3f-46bb-93a1-b54d66196e6b
-- title:
--   BBSampling Diagonal
-- statement:
--   Definitions and structural lemmas for BBSampling Diagonal, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BBSamplingDiagonal.lean

import Definitions.Def_Tablet_SLLNCurves
import Definitions.Def_Tablet_CountableDiagonalExtraction
import Definitions.Def_Tablet_EtaRepeats
import Definitions.Def_Tablet_EtaRepeatsTilde
import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_PsiMeasurable
import Definitions.Def_Tablet_PsiTildeMeasurable
import Definitions.Def_Tablet_PsiUniformBound
import Definitions.Def_Tablet_PsiTildeUniformBound
import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Theorems.Thm_CountableDiagonalExtraction
import Theorems.Thm_CurveScaledEvalMeasurable
import Theorems.Thm_EtaRepeats
import Theorems.Thm_EtaRepeatsTilde
import Theorems.Thm_PsiMeasurable
import Theorems.Thm_PsiTildeMeasurable
import Theorems.Thm_PsiTildeUniformBound
import Theorems.Thm_PsiUniformBound
import Theorems.Thm_SLLNCurves

set_option autoImplicit false
open MeasureTheory Filter Finset ENNReal



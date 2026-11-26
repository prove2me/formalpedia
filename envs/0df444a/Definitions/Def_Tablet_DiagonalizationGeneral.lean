-- Prove2me | Definitions.Def_Tablet_DiagonalizationGeneral
-- name    : Tablet_DiagonalizationGeneral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:03:38.036318+00:00
-- url     : https://prove2.me/theorems/8754df8b-5e09-44e0-8e66-0bcc7cecb48d
-- title:
--   Diagonalization General
-- statement:
--   Definitions and structural lemmas for Diagonalization General, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/DiagonalizationGeneral.lean

import Definitions.Def_Tablet_MetricCurrent1
import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_LipschitzSeparable
import Definitions.Def_Tablet_CurrentFormAddF
import Definitions.Def_Tablet_CurrentTwoFormEstimate
import Definitions.Def_Tablet_CurrentFormAddPi
import Definitions.Def_Tablet_PiBoundsF
import Definitions.Def_Tablet_PiBoundsPi
import Definitions.Def_Tablet_PsiVanishes
import Definitions.Def_Tablet_CurrentContinuousF
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_psiTilde
import Theorems.Thm_CurrentContinuousF
import Theorems.Thm_CurrentFormAddF
import Theorems.Thm_CurrentFormAddPi
import Theorems.Thm_CurrentTwoFormEstimate
import Theorems.Thm_LipschitzSeparable
import Theorems.Thm_PiBoundsF
import Theorems.Thm_PiBoundsPi
import Theorems.Thm_PsiVanishes

set_option autoImplicit false
open Set Filter Finset MeasureTheory ENNReal
open scoped NNReal



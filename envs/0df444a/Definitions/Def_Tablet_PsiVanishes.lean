-- Prove2me | Definitions.Def_Tablet_PsiVanishes
-- name    : Tablet_PsiVanishes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:57:53.690099+00:00
-- url     : https://prove2.me/theorems/dde85058-e4f2-57a3-860b-acb689e93d1b
-- title:
--   Psi Vanishes
-- statement:
--   Definitions and structural lemmas for Psi Vanishes, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/PsiVanishes.lean

import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_PsiMeasurable
import Definitions.Def_Tablet_PsiTildeMeasurable
import Theorems.Thm_PsiMeasurable
import Theorems.Thm_PsiTildeMeasurable

set_option autoImplicit false
open MeasureTheory Filter Topology



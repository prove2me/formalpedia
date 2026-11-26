-- Prove2me | Definitions.Def_Tablet_LipschitzSeparable
-- name    : Tablet_LipschitzSeparable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:54:01.389789+00:00
-- url     : https://prove2.me/theorems/4af63f9b-1cd6-4e21-b0e7-8158c13b968d
-- title:
--   Lipschitz Separable
-- statement:
--   Definitions and structural lemmas for Lipschitz Separable, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/LipschitzSeparable.lean

import Definitions.Def_Tablet_ConeInterpolation
import Definitions.Def_Tablet_RationalCompatibleValues
import Theorems.Thm_ConeInterpolation
import Theorems.Thm_RationalCompatibleValues

set_option autoImplicit false
open scoped NNReal
open Filter Topology



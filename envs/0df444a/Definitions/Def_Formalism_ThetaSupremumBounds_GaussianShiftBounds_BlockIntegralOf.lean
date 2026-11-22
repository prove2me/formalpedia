-- Prove2me | Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_BlockIntegralOf
-- name    : Formalism_ThetaSupremumBounds_GaussianShiftBounds_BlockIntegralOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:58:23.047399+00:00
-- url     : https://prove2.me/theorems/35ee044a-7ffe-4150-b15b-f06d4d9ee0e8
-- title:
--   Block Integral Of
-- statement:
--   Definitions and structural lemmas for Block Integral Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/GaussianShiftBounds/BlockIntegralOf.lean

import Mathlib
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialSandwich
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory
open scoped ComplexConjugate Real
namespace Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
end Formalism.DimensionVariation



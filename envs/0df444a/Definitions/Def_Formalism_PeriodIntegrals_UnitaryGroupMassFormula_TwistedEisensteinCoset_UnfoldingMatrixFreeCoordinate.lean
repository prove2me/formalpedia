-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnfoldingMatrixFreeCoordinate
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnfoldingMatrixFreeCoordinate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:42.136555+00:00
-- url     : https://prove2.me/theorems/1000044a-81f2-4c6e-b03b-c00c2193f935
-- title:
--   Unfolding Matrix Free Coordinate
-- statement:
--   Definitions and structural lemmas for Unfolding Matrix Free Coordinate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/UnfoldingMatrixFreeCoordinate.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
namespace PI.TwistedEisensteinNonvanishing.W
open Loc LocE
section Vec
variable {E : Type} [Field E]
end Vec
section Bd
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
end Bd
end PI.TwistedEisensteinNonvanishing.W



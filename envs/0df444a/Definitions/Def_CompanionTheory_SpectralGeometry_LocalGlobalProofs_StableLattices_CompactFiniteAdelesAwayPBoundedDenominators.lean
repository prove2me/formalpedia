-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CompactFiniteAdelesAwayPBoundedDenominators
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CompactFiniteAdelesAwayPBoundedDenominators
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:08:17.001679+00:00
-- url     : https://prove2.me/theorems/1d5ca2f2-4522-43d1-b180-20be6a370486
-- title:
--   Compact Finite Adeles Away PBounded Denominators
-- statement:
--   Definitions and structural lemmas for Compact Finite Adeles Away PBounded Denominators, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CompactFiniteAdelesAwayPBoundedDenominators.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
namespace GlobalTheory.CompanionTheory.KModExists
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open PI.UpqRep (IsKFin IsKTypeOf IsKStableOn)
open CompanionTheory.D.DSIC
end GlobalTheory.CompanionTheory.KModExists



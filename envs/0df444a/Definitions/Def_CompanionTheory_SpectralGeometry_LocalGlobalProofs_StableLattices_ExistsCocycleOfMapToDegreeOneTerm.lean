-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsCocycleOfMapToDegreeOneTerm
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsCocycleOfMapToDegreeOneTerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:37.696503+00:00
-- url     : https://prove2.me/theorems/bdf0e6e7-9f0a-4302-a710-acd4a11a9cad
-- title:
--   Exists Cocycle Of Map To Degree One Term
-- statement:
--   Definitions and structural lemmas for Exists Cocycle Of Map To Degree One Term, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistsCocycleOfMapToDegreeOneTerm.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.CompanionTheory.ChainHighest
open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
open PI.UpqRep (lowK)
end GlobalTheory.CompanionTheory.ChainHighest



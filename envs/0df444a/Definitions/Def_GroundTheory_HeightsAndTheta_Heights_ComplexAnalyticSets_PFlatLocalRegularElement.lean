-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatLocalRegularElement
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatLocalRegularElement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:45.756474+00:00
-- url     : https://prove2.me/theorems/ac7ead47-0230-426f-a246-456ae3123e19
-- title:
--   PFlat Local Regular Element
-- statement:
--   Definitions and structural lemmas for PFlat Local Regular Element, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFlatLocalRegularElement.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularElement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing TensorProduct
open scoped Pointwise
section Flat
variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
end Flat
section Local
variable {A B M : Type} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
variable [IsNoetherianRing A] [IsLocalRing A] [Module.Flat A M]
variable [IsNoetherianRing B] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Module.Finite B M]
end Local
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets



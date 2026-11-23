-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:00:33.265718+00:00
-- url     : https://prove2.me/theorems/1fb7c428-0fbf-464d-b5d9-ca63e2c1e779
-- title:
--   Car Imp Frel
-- statement:
--   Definitions and structural lemmas for Car Imp Frel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CarImpFrel.lean

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
open Finset CompanionTheory.D.DSIC
noncomputable section
namespace GlobalTheory.CompanionTheory.DSICFRel
def bil {ι A : Type} [Fintype ι] [Ring A] [Algebra ℂ A] (c a : ι → A) (m : ι → ι → ℂ) : A :=
  ∑ i, ∑ j, m i j • (c i * a j)
variable {n : ℕ}
def dl (x y : Fin n) : ℂ := if x = y then 1 else 0
def mm (c d : Fin n) (x y : Fin n × Fin n) : ℂ :=
  dl x.1 c * dl y.1 d * dl x.2 y.2 - dl x.2 d * dl y.2 c * dl x.1 y.1
section
variable {ε : Fin n → Bool} {V : Type} [AddCommGroup V] [Module ℂ V]
end
end GlobalTheory.CompanionTheory.DSICFRel



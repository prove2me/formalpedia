-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FibAc
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FibAc
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:37:06.830373+00:00
-- url     : https://prove2.me/theorems/2cf4fddc-6e1d-435c-bc36-6bd444c70d01
-- title:
--   Fib Ac
-- statement:
--   Definitions and structural lemmas for Fib Ac, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/FibAc.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
namespace GlobalTheory.CompanionTheory.PointSurjectivity
def FibAc {R : Type} [CommRing R] {X : Scheme.{0}} (a : X ⟶ Spec (CommRingCat.of R)) (N : LB X) : Prop :=
  ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ →
    (cechLB a N D).Acyclic
end GlobalTheory.CompanionTheory.PointSurjectivity



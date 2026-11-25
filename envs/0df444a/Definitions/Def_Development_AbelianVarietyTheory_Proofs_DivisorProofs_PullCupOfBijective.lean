-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullCupOfBijective
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PullCupOfBijective
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T14:38:50.906115+00:00
-- url     : https://prove2.me/theorems/6da1e1b6-3ea7-4cdc-8822-191f26e3cc13
-- title:
--   Pull Cup Of Bijective
-- statement:
--   Definitions and structural lemmas for Pull Cup Of Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PullCupOfBijective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace GlobalTheory.PullbackCupProduct
open GlobalTheory.CatCoh
universe u v u' v' u'' v''
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : AlgebraicGeometry.Scheme}
  {s : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} {s' : X' ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R'} {σ : R →+* R'}
  {φ : X' ⟶ X}
end GlobalTheory.PullbackCupProduct



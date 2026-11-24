-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffinePairRestrictionInjectiveFirstCohomology
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffinePairRestrictionInjectiveFirstCohomology
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T17:09:00.4498+00:00
-- url     : https://prove2.me/theorems/7ed61a65-6e35-4b81-ba54-7377accae58f
-- title:
--   Affine Pair Restriction Injective First Cohomology
-- statement:
--   Definitions and structural lemmas for Affine Pair Restriction Injective First Cohomology, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffinePairRestrictionInjectiveFirstCohomology.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueFunctionsAffineOpenFromPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneFormEqZeroOfVanishingOnPairsStatement
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
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
namespace GlobalTheory.CechDR
open Opposite KaehlerDifferential
variable {R' : Type} [CommRing R'] {X X' : Scheme.{0}}
end GlobalTheory.CechDR
namespace GlobalTheory.CechDR
open Opposite KaehlerDifferential
end GlobalTheory.CechDR



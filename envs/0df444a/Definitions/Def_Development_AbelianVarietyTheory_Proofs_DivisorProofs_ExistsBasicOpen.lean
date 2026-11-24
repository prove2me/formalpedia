-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T15:55:33.856186+00:00
-- url     : https://prove2.me/theorems/2ad11b23-0853-46b4-95cc-b58ae731e913
-- title:
--   Exists Basic Open
-- statement:
--   Definitions and structural lemmas for Exists Basic Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasicOpen.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace GlobalTheory.CechDR
variable {X X' : Scheme.{0}}
end GlobalTheory.CechDR
namespace GlobalTheory.CechDR
open Opposite
variable {R' : Type} [CommRing R'] {X X' : Scheme.{0}}
end GlobalTheory.CechDR



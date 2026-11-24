-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CochainValueOnThickeningHomEqSubOfGlued
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CochainValueOnThickeningHomEqSubOfGlued
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T16:56:30.974811+00:00
-- url     : https://prove2.me/theorems/67bf2f9f-a0bd-4f71-b4ca-34768f993f6f
-- title:
--   Cochain Value On Thickening Hom Eq Sub Of Glued
-- statement:
--   Definitions and structural lemmas for Cochain Value On Thickening Hom Eq Sub Of Glued, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CochainValueOnThickeningHomEqSubOfGlued.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecFunctionsEqOfRestrictionsOnPairsStatement
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
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
namespace GlobalTheory.CechDR.AffLoc
section Lemmas
variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
instance mono_affPt (s : X ⟶ Sp R) (U : X.affineOpens) : Mono (affPt s U) := by
  change Mono U.2.fromSpec
  have := IsAffineOpen.isOpenImmersion_fromSpec U.2
  exact IsOpenImmersion.mono _
end Lemmas
end GlobalTheory.CechDR.AffLoc



-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TwistedPowTranslate
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TwistedPowTranslate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:35:56.01982+00:00
-- url     : https://prove2.me/theorems/b3c62ff3-259f-47b4-89e3-c4d6f63d5619
-- title:
--   Twisted Pow Translate
-- statement:
--   Definitions and structural lemmas for Twisted Pow Translate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TwistedPowTranslate.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TwistTranslate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
section Gen
variable {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
end Gen
variable {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] (t : Spec (CommRingCat.of K) ⟶ S)
end GlobalTheory.TwistTranslate
namespace GlobalTheory
end GlobalTheory



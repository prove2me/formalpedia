-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenTranslEqPairing
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenTranslEqPairing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:06.277544+00:00
-- url     : https://prove2.me/theorems/1a00c11b-c1da-4e9f-8178-c363a256906e
-- title:
--   Exists Gen Transl Eq Pairing
-- statement:
--   Definitions and structural lemmas for Exists Gen Transl Eq Pairing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenTranslEqPairing.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.DescentPairing
section Alg
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h
end Alg
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)
end GlobalTheory.DescentPairing



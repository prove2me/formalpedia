-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChart
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:31:15.856404+00:00
-- url     : https://prove2.me/theorems/c3a35487-840a-4276-a5f7-ecd701e68c92
-- title:
--   Exists Scheme Model Of Affine Smooth Chart
-- statement:
--   Definitions and structural lemmas for Exists Scheme Model Of Affine Smooth Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSchemeModelOfAffineSmoothChart.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.ChartModel
set_option backward.isDefEq.respectTransparency false
noncomputable def twoCover {X U V : Scheme.{0}} (u : U ⟶ X) (v : V ⟶ X) [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) : X.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun i => Bool.rec U V i)
    (fun i => Bool.rec (motive := fun i => (Bool.rec U V i : Scheme.{0}) ⟶ X) u v i) (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩) (fun i => by cases i <;> assumption)
end GlobalTheory.ChartModel



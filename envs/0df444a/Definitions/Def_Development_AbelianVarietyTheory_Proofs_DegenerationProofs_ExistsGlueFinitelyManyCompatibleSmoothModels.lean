-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModels
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModels
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:53.285918+00:00
-- url     : https://prove2.me/theorems/05816060-b253-49a4-9639-3df55805e375
-- title:
--   Exists Glue Finitely Many Compatible Smooth Models
-- statement:
--   Definitions and structural lemmas for Exists Glue Finitely Many Compatible Smooth Models, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsGlueFinitelyManyCompatibleSmoothModels.lean

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
namespace GlobalTheory.SS.GlueCompat
set_option backward.isDefEq.respectTransparency false
noncomputable def coverTwo {X U V : Scheme.{0}} (u : U ⟶ X) (v : V ⟶ X) [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) : X.OpenCover :=
  let T : Bool → Scheme.{0} := fun i => Bool.rec U V i
  let t : ∀ i, T i ⟶ X := fun i => Bool.rec (motive := fun i => T i ⟶ X) u v i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}
noncomputable def ofSquare (Y : Over (Sp R)) (h₁ : Smooth Y.hom) (h₂ : IsSeparated Y.hom) (h₃ : QuasiCompact Y.hom)
    {j : A.left ⟶ Y.left} (h : IsPullback j A.hom Y.hom (spMap (algebraMap R K))) : Model R A :=
  ⟨Y, Over.isoMk h.isoPullback.symm (h.isoPullback_inv_snd), h₁, h₂, h₃⟩
variable [IsDomain R] [IsFractionRing R K]
end GlobalTheory.SS.GlueCompat



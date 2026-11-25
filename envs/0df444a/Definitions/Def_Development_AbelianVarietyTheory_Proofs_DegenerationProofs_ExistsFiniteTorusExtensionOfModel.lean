-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T15:18:41.273534+00:00
-- url     : https://prove2.me/theorems/9f702c0c-ba17-409e-8111-1b1f8b18c354
-- title:
--   Exists Finite Torus Extension Of Model
-- statement:
--   Definitions and structural lemmas for Exists Finite Torus Extension Of Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFiniteTorusExtensionOfModel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomDescendsToSubfieldContainingFinsetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFinsetModelOfIsAffineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupSchemeMorphismDescendsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusExtensionDescendsStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.FieldModel
def HasModel {K : Type} [Field K] (X : Over (Sp K)) : Prop :=
  ∃ s : Finset K, ∀ (k : Type) [Field k] (β : k →+* K), (s : Set K) ⊆ Set.range β →
    ∃ (X₀ : Over (Sp k)) (φ : X.left ⟶ X₀.left), IsPullback φ X.hom X₀.hom (spMap β)
variable {K : Type} [Field K]
abbrev part (X : Over (Sp K)) (U : X.left.Opens) : Over (Sp K) := Over.mk (U.ι ≫ X.hom)
abbrev partMap (X : Over (Sp K)) {U V : X.left.Opens} (h : U ≤ V) : part X U ⟶ part X V :=
  Over.homMk (X.left.homOfLE h) (by simp)
section Square
variable {S S₀ : Scheme.{0}} {c : S ⟶ S₀} {B : Over S} {B₀ : Over S₀} {φ : B.left ⟶ B₀.left}
def sq (w : φ ≫ B₀.hom = B.hom ≫ c) : (B ⊗ B).left ⟶ (B₀ ⊗ B₀).left :=
  pullback.map B.hom B.hom B₀.hom B₀.hom φ φ c w.symm w.symm
end Square
end GlobalTheory.FieldModel
namespace GlobalTheory
end GlobalTheory



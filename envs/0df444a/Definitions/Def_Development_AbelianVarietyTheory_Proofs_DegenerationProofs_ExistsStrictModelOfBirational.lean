-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStrictModelOfBirational
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStrictModelOfBirational
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:56:42.346107+00:00
-- url     : https://prove2.me/theorems/3172d142-c8e4-4ab7-a281-803ae45f44fc
-- title:
--   Exists Strict Model Of Birational
-- statement:
--   Definitions and structural lemmas for Exists Strict Model Of Birational, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStrictModelOfBirational.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeronStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOnPoints
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
noncomputable section
namespace GlobalTheory.SS.StrictLaw
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
def pr₁ (M : Model R A) (N : Model R A') : (M.prod N).Y ⟶ M.Y := fst M.Y N.Y
def pr₂ (M : Model R A) (N : Model R A') : (M.prod N).Y ⟶ N.Y := snd M.Y N.Y
def Good (M : Model R A) (f : A ⊗ A ⟶ A ⊗ A) (V : Set M.Y.left) (z : (M.prod M).Y.left) : Prop :=
  ∃ (U : (M.prod M).Y.left.Opens) (g : U.toScheme ⟶ (M.prod M).Y.left) (u : U.toScheme),
    Extends (M.prod M) (M.prod M) f U g ∧ IsOpenImmersion g ∧ U.ι u = z ∧
    (pr₁ M M).left z ∈ V ∧ (pr₂ M M).left z ∈ V ∧
    (pr₁ M M).left (g u) ∈ V ∧ (pr₂ M M).left (g u) ∈ V
section
variable [IsDomain R] [IsLocalRing R] [IsFractionRing R K]
  [IsAlgClosed (IsLocalRing.ResidueField R)]
end
def coshear (A : Over (Sp K)) [GrpObj A] : Bool → (A ⊗ A ⟶ A ⊗ A)
  | true => (β_ A A).hom ≫ shear A true ≫ (β_ A A).hom
  | false => (ι[A] ⊗ₘ 𝟙 A) ≫ (β_ A A).hom ≫ shear A true ≫ (β_ A A).hom
end GlobalTheory.SS.StrictLaw
namespace GlobalTheory.SS
open StrictLaw
end GlobalTheory.SS
end



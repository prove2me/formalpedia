-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleGlobalSectionsFunctionFieldIff
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleGlobalSectionsFunctionFieldIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:33.317286+00:00
-- url     : https://prove2.me/theorems/78438d38-07bf-4e6c-b546-5b4dadc36383
-- title:
--   Line Bundle Global Sections Function Field Iff
-- statement:
--   Definitions and structural lemmas for Line Bundle Global Sections Function Field Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LineBundleGlobalSectionsFunctionFieldIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
open GlobalTheory.AbLaw (rs pw)
noncomputable section
namespace GlobalTheory.VolFin
variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
def gen (U : X.Opens) (h : genericPoint X ∈ U) : Γ(X, U) →+* X.functionField :=
  (X.presheaf.germ U _ h).hom
theorem generic_mem {U : X.Opens} {x : X} (hx : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 ⟨x, trivial, hx⟩
def tr (N : LB X) (i j : N.ι) (hi : genericPoint X ∈ N.U i) (hj : genericPoint X ∈ N.U j) :
    X.functionField := gen (N.U i ⊓ N.U j) ⟨hi, hj⟩ (N.g i j).val
def ffMap (ψ : X ⟶ Y) (hψ : ψ (genericPoint X) = genericPoint Y) :
    Y.functionField →+* X.functionField :=
  (Y.presheaf.stalkSpecializes (x := ψ (genericPoint X)) (y := genericPoint Y)
    (hψ ▸ specializes_rfl) ≫ ψ.stalkMap (genericPoint X)).hom
end GlobalTheory.VolFin



-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:53.341132+00:00
-- url     : https://prove2.me/theorems/4f90d79b-0e71-4e48-8098-4b0f393c86d1
-- title:
--   Arith Model
-- statement:
--   Definitions and structural lemmas for Arith Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
set_option linter.unusedSectionVars false
namespace ProjLine
section Homog
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
end Homog
abbrev Kfr : Type := FractionRing (MRing (GlobalTheory (Fin 2)))
abbrev Xk (i : Fin 2) : Kfr := algebraMap (MRing (GlobalTheory (Fin 2))) Kfr (X ⟨(), i⟩)
def u : Kfr := Xk 1 / Xk 0
abbrev FnField : Type := Subfield.closure ({u} : Set Kfr)
def uF : FnField := ⟨u, Subfield.subset_closure rfl⟩
def y : Ix (Fin 2) → FnField := fun p => ![1, uF] p.2
abbrev incl : FnField →+* Kfr := (Subfield.closure ({u} : Set Kfr)).subtype
section FS
open scoped Topology
variable {J : Type} [Fintype J]
abbrev eL : (J → ℂ) →L[ℝ] EuclideanSpace ℂ J :=
  ((EuclideanSpace.equiv J ℂ).symm.toContinuousLinearMap).restrictScalars ℝ
def reInner : (J → ℂ) →L[ℝ] ((J → ℂ) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (J → ℂ) (EuclideanSpace ℂ J) ℝ).flip eL).comp
    ((innerSL ℝ (E := EuclideanSpace ℂ J)).comp eL)
def normSqE (z : J → ℂ) : ℝ := ‖eL z‖ ^ 2
end FS
end ProjLine
end
end GroundTheory.Heights₂.Heights.HilbertSamuel



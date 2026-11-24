-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:33.647858+00:00
-- url     : https://prove2.me/theorems/3c9da291-8a46-4aa5-940d-120fb95a60ea
-- title:
--   Ex Map
-- statement:
--   Definitions and structural lemmas for Ex Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExMap.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
def pointFormEuler_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι) (n : ℕ)
    (F : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y x : Fin n → ℂ) (c : K → ℂ),
    IsSmoothHerm A → AnalyticAt ℂ F y → (∀ k, ∃ i, F y ⟨k, i⟩ ≠ 0) → fderiv ℂ F y x = bsmul c (F y) →
    cxHessian (fun y' => Real.log (A.h (F y'))) y *ᵥ star x = 0
def pointFormEuler_holds.exLin : (Fin 1 → ℂ) →L[ℂ] ((Σ k, IndefiniteRowSideFullHecke.Inter.GlobalTheory 2 k) → ℂ) :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.proj 0
def pointFormEuler_holds.exMap (y' : Fin 1 → ℂ) : (Σ k, IndefiniteRowSideFullHecke.Inter.GlobalTheory 2 k) → ℂ :=
  (fun _ => (1 : ℂ)) + pointFormEuler_holds.exLin y'
end GroundTheory.Heights₂.Heights.Inter



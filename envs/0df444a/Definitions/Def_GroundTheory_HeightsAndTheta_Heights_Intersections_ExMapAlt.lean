-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMapAlt
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ExMapAlt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:18.664878+00:00
-- url     : https://prove2.me/theorems/c661baa6-fa19-4122-89e3-07d43a002861
-- title:
--   Ex Map Alt
-- statement:
--   Definitions and structural lemmas for Ex Map Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ExMapAlt.lean

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
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
def pointFormRank_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (d n : ℕ)
    (F : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y : Fin n → ℂ),
    IsArithVar Q d → d ≤ n → AnalyticAt ℂ F y → (∀ᶠ y' in 𝓝 y, F y' ∈ mcPts Q) →
    ∃ x : Fin n → ℂ, x ≠ 0 ∧ ∃ c : K → ℂ, fderiv ℂ F y x = bsmul c (F y)
def pointFormRank_holds.exLin : (Fin 2 → ℂ) →L[ℂ] ((Σ k, IndefiniteRowSideFullHecke.Inter.GlobalTheory 2 k) → ℂ) :=
  ContinuousLinearMap.pi fun p => ContinuousLinearMap.proj p.2
def pointFormRank_holds.exMap (y' : Fin 2 → ℂ) : (Σ k, IndefiniteRowSideFullHecke.Inter.GlobalTheory 2 k) → ℂ :=
  (fun _ => (1 : ℂ)) + pointFormRank_holds.exLin y'
end GroundTheory.Heights₂.Heights.Inter



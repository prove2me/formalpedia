-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeviOfRealSmulRight
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_LeviOfRealSmulRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:12:01.002556+00:00
-- url     : https://prove2.me/theorems/b499e59a-837b-44fa-b0d8-17ecb760c4c6
-- title:
--   Levi Of Real Smul Right
-- statement:
--   Definitions and structural lemmas for Levi Of Real Smul Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
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
open Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
namespace pointFormEuler_holds
section Levi
variable {n : ℕ}
def leviOf (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v : Fin n → ℂ) : ℂ :=
  ((H u v + H (Complex.I • u) (Complex.I • v) : ℝ) +
    Complex.I * ((H u (Complex.I • v) - H (Complex.I • u) v : ℝ))) / 4
end Levi
section Ambient
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def bsmulCLM (d : K → ℂ) : ((Σ k, ι k) → ℂ) →L[ℂ] ((Σ k, ι k) → ℂ) :=
  ContinuousLinearMap.pi fun p => d p.1 • ContinuousLinearMap.proj p
end Ambient
section Chain
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}
end Chain
end pointFormEuler_holds
end GroundTheory.Heights₂.Heights.Inter



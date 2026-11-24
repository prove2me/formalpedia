-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveDegreeVert
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveDegreeVert
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:12.053683+00:00
-- url     : https://prove2.me/theorems/5aef9194-4986-481c-a74b-2aded3126798
-- title:
--   Statements Curve Degree Vert
-- statement:
--   Definitions and structural lemmas for Statements Curve Degree Vert, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsCurveDegreeVert.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_SameOrbitOneSpecZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CurveCountObjects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter
def CurveDegreeVert.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem) (c : ∀ k, ι k)
    (R : Finset ((Σ k, ι k) → ℂ)) (b d : K → ℕ),
    IsIntersectionSystem II → IsArithVar P 1 → IsSmoothHerm A → (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) →
    (∀ t ∈ R, t ∈ mcPts P) → (∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t) →
    (∀ k, (d k : ℤ) = A.a k + b k) →
    II K ι P 1 (fun _ => A) =
      vertR P (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c d) -
        vertR P (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c b) +
        ∑ t ∈ R, Real.log (chartRadius A c t)
namespace CurveDegreeVert
end CurveDegreeVert
end GroundTheory.Heights₂.Heights.Targets



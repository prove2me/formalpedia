-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherLast
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherLast
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:38.099276+00:00
-- url     : https://prove2.me/theorems/29ee3def-8c54-4dc1-a587-513e3d2a7fcd
-- title:
--   Imports Further Last
-- statement:
--   Definitions and structural lemmas for Imports Further Last, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ImportsFurtherLast.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def regularityPointsSum_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 →
    ∃ R : Finset ((Σ k, ι k) → ℂ), (∀ t ∈ R, t ∈ mcPts P) ∧
      (∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t) ∧
      ∀ h : ((Σ k, ι k) → ℂ) → ℝ,
        (∀ z z', z ∈ mcPts P → SameOrbit z z' → h z = h z') →
        ptsIntegral P (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) h = ∑ t ∈ R, h t
end
end GroundTheory.Heights₂.Heights.Inter



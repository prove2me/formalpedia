-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CoordCurveDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CoordCurveDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:25.712326+00:00
-- url     : https://prove2.me/theorems/ba928689-17c2-4dcd-9307-8c36177d5066
-- title:
--   Coord Curve Degree
-- statement:
--   Definitions and structural lemmas for Coord Curve Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/CoordCurveDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
def CoordCurveDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω), IsArithVar (mCoordIdeal y) 1 →
      degC (mCoordIdeal y) = Nat.card (blockFnField y →ₐ[ℚ] ℂ)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet



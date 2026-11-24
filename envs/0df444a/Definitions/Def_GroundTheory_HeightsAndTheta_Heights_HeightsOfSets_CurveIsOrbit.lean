-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:22.479129+00:00
-- url     : https://prove2.me/theorems/b02da4ec-2163-4e6c-a4d3-8deb3085e8db
-- title:
--   Curve Is Orbit
-- statement:
--   Definitions and structural lemmas for Curve Is Orbit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/CurveIsOrbit.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
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
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G
def CurveIsOrbit.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (W : Ideal (MvPolynomial (Coord n) ℤ)),
    Geo.IsArithVar (ι := blockIdx n) W 1 →
      ∃ x : Cone n (AlgebraicClosure ℚ), BlockNonzero x ∧ W = orbitIdeal x
end GroundTheory.Heights₂.Heights



-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StReducedBasisBound
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StReducedBasisBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:04:03.992803+00:00
-- url     : https://prove2.me/theorems/e1895615-eb4b-4ff9-9241-603317e6e115
-- title:
--   St Reduced Basis Bound
-- statement:
--   Definitions and structural lemmas for St Reduced Basis Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StReducedBasisBound.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open Module MeasureTheory
noncomputable section
def ReducedBasisBound.Statement : Prop :=
  ∀ (d : ℕ) (t c : ℝ), 0 < t → ∃ C : ℝ, ∀ (L : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology L] [IsZLattice ℝ L], (∀ x ∈ L, x ≠ 0 → t ≤ ‖x‖) →
      ZLattice.covolume L ≤ c → ∃ b : Basis (Fin d) ℤ L, ∀ i, ‖(b i : EuclideanSpace ℝ (Fin d))‖ ≤ C
end
end GroundTheory.Heights₂.Heights.FiniteCovolume



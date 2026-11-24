-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOneComponentGeneralPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOneComponentGeneralPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:43.606527+00:00
-- url     : https://prove2.me/theorems/d45065a1-5929-42e5-ac78-f641ec0de99a
-- title:
--   St One Component General Point
-- statement:
--   Definitions and structural lemmas for St One Component General Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StOneComponentGeneralPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsBranchesGoodPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology
noncomputable section
def OneComponentGeneralPoint.Statement : Prop :=
  ∀ (n : ℕ) (I W : Ideal (MvPolynomial (Fin n) ℂ)), W ∈ I.minimalPrimes →
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧
      GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ⊆
        closure (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ U) ∧
      ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ U, ∃ N ∈ 𝓝 x,
        GroundTheory.Heights₂.Heights.ComplexSets.zeroSet I ∩ N ⊆ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets



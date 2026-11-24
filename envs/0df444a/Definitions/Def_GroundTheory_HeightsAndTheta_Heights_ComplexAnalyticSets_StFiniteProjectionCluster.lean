-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionCluster
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionCluster
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:51.023746+00:00
-- url     : https://prove2.me/theorems/a2b73521-7a38-4b44-9239-daf9a9f4b61a
-- title:
--   St Finite Projection Cluster
-- statement:
--   Definitions and structural lemmas for St Finite Projection Cluster, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StFiniteProjectionCluster.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Topology
noncomputable section
def FiniteProjectionCluster.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (w : Fin n → ℂ)
    (U : Set (Fin n → ℂ)),
    IsFiniteProjection J A → w ∈ zeroSet J → U ∈ 𝓝 w →
      ∃ (r : ℝ) (N M : Set (Fin n → ℂ)), 0 < r ∧ IsOpen N ∧ IsOpen M ∧ w ∈ N ∧ N ⊆ U ∧
        Disjoint N M ∧
        zeroSet J ∩ {x | A.mulVec x ∈ Metric.ball (A.mulVec w) r} ⊆ N ∪ M ∧
        Bornology.IsBounded (zeroSet J ∩ {x | A.mulVec x ∈ Metric.ball (A.mulVec w) r})
end
end GroundTheory.Heights₂.Heights.ComplexSets



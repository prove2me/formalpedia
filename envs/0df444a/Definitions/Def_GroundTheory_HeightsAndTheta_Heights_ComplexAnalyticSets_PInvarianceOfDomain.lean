-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInvarianceOfDomain
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInvarianceOfDomain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:18.832897+00:00
-- url     : https://prove2.me/theorems/2671b779-7eae-4154-af45-f32bf58ac9f5
-- title:
--   PInvariance Of Domain
-- statement:
--   Definitions and structural lemmas for PInvariance Of Domain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PInvarianceOfDomain.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInvarianceOfDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBrouwerFixedPoint
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
namespace InvarianceOfDomain
open Metric Set MeasureTheory
variable {n : ℕ}
def smoothSubalgebra (n : ℕ) : Subalgebra ℝ C(Fin n → ℝ, ℝ) where
  carrier := {g | ContDiff ℝ 1 (g : (Fin n → ℝ) → ℝ)}
  mul_mem' {g h} hg hh := by
    simp only [mem_ofPred_eq, ContinuousMap.coe_mul]
    exact ContDiff.mul hg hh
  add_mem' {g h} hg hh := by
    simp only [mem_ofPred_eq, ContinuousMap.coe_add]
    exact ContDiff.add hg hh
  algebraMap_mem' c := by
    simp only [mem_ofPred_eq]
    convert (contDiff_const (c := c) : ContDiff ℝ 1 fun _ : Fin n → ℝ => c) using 1
    ext x
    simp
noncomputable def radialPush (c : Fin n → ℝ) (ρ : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  c + max 1 (ρ / ‖y - c‖) • (y - c)
end InvarianceOfDomain
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets



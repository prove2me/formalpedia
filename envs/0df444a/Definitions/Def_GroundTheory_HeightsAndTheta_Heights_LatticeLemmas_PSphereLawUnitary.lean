-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawUnitary
-- name    : GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereLawUnitary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:00.919937+00:00
-- url     : https://prove2.me/theorems/7ed5c646-3ec7-44eb-a529-b2997fef0f48
-- title:
--   PSphere Law Unitary
-- statement:
--   Definitions and structural lemmas for PSphere Law Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSphereLawUnitary.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
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
open MeasureTheory ProbabilityTheory
noncomputable section
namespace SphereLawUnitary
def rowMap {N : ℕ} (k : ℕ) (U : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) :
    (Fin k × Fin N → ℂ) →ₗ[ℝ] (Fin k × Fin N → ℂ) where
  toFun u ij := U (fun j ↦ u (ij.1, j)) ij.2
  map_add' u v := by
    funext ij
    have : (fun j ↦ (u + v) (ij.1, j)) = (fun j ↦ u (ij.1, j)) + fun j ↦ v (ij.1, j) := rfl
    change U (fun j ↦ (u + v) (ij.1, j)) ij.2 =
      U (fun j ↦ u (ij.1, j)) ij.2 + U (fun j ↦ v (ij.1, j)) ij.2
    rw [this, map_add]
    rfl
  map_smul' r u := by
    funext ij
    have : (fun j ↦ (r • u) (ij.1, j)) = (r : ℂ) • fun j ↦ u (ij.1, j) := by
      funext j; simp [Complex.real_smul]
    change U (fun j ↦ (r • u) (ij.1, j)) ij.2 = r • U (fun j ↦ u (ij.1, j)) ij.2
    rw [this, map_smul]
    simp [Complex.real_smul]
end SphereLawUnitary
end
end GroundTheory.Heights₂.Heights



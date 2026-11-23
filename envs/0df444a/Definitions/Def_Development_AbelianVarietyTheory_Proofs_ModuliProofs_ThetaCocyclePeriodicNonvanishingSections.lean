-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSections
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:26:23.585891+00:00
-- url     : https://prove2.me/theorems/9d90fe51-66ff-4551-8b3a-3ae5f242d679
-- title:
--   Theta Cocycle Periodic Nonvanishing Sections
-- statement:
--   Definitions and structural lemmas for Theta Cocycle Periodic Nonvanishing Sections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ThetaCocyclePeriodicNonvanishingSections.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SetIntegralFderivEqZeroOfLatticePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open Filter Topology
namespace GlobalTheory.PeriodSymm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
noncomputable def dbar (f : E → ℂ) (u : E) (z : E) : ℂ :=
  fderiv ℝ f z u + I * fderiv ℝ f z (I • u)
noncomputable def antiRow {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (m : Fin g) :
    (Fin g → ℂ) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => M.mulVec (star z) m
      map_add' := fun x y => by simp [star_add, Matrix.mulVec_add]
      map_smul' := fun r x => by
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm] }
end GlobalTheory.PeriodSymm



-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:38.763585+00:00
-- url     : https://prove2.me/theorems/272ed3a0-2c01-4425-b7b9-8722945ab647
-- title:
--   First Kernel Properties Of Hypotheses
-- statement:
--   Definitions and structural lemmas for First Kernel Properties Of Hypotheses, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val


set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P
namespace A5x6
section KRfacts
variable {K : Type} [CommRing K] (R : Subring K)
theorem mem_rangeR (a : K) : a ∈ LinearMap.range (Algebra.linearMap R K) ↔ a ∈ R := by
  constructor
  · intro h
    obtain ⟨r, rfl⟩ := LinearMap.mem_range.mp h
    exact r.2
  · intro ha
    exact LinearMap.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩
theorem latZ_le_ker {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) :
    latZ R Z ≤ LinearMap.ker (lamLin R Z) := by
  intro v hv
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hv)
  rw [LinearMap.mem_ker]
  simp only [lamLin, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [← hw]
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hZ, Matrix.one_mulVec]
  rw [mem_rangeR]
  unfold lastCoord
  rw [LinearMap.sum_apply]
  refine R.sum_mem fun j _ => ?_
  split_ifs
  · simp [coeLin]
    exact (w j).2
  · simp
def muZ {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) : coker R Z →ₗ[R] KR R :=
  (latZ R Z).liftQ (lamLin R Z) (latZ_le_ker R Z hZ)
end KRfacts
end A5x6
open A5x6
end Formalism.FourierDecayAlt.P



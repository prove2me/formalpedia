-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantEtaleTraceAddCharHermitianKerne
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantEtaleTraceAddCharHermitianKerne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:27.952123+00:00
-- url     : https://prove2.me/theorems/4ffcca1a-2232-4863-8342-73961fb59a0b
-- title:
--   Is Locally Constant Etale Trace Add Char Hermitian Kerne
-- statement:
--   Definitions and structural lemmas for Is Locally Constant Etale Trace Add Char Hermitian Kerne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocallyConstantEtaleTraceAddCharHermitianKerne.lean

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.Hyp
def kerLinF {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    (A : Et F E) (x : A.K) (y' : A.L) : A.L →ₗ[F] F where
  toFun y := Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y * y'))
  map_add' a b := by simp [star_add, add_mul, mul_add, map_add]
  map_smul' c a := by
    have hc : star (algebraMap F A.L c) = algebraMap F A.L c := by
      rw [IsScalarTower.algebraMap_apply F A.K A.L]; exact A.star_K _
    have h1 : star (c • a) * y' = (algebraMap F A.K c) • (star a * y') := by
      rw [Algebra.smul_def, star_mul, hc, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]; ring
    rw [h1, map_smul, smul_eq_mul, ← mul_assoc, mul_comm x, mul_assoc, ← Algebra.smul_def, map_smul]
    rfl
end GlobalTheory.JR.Hyp



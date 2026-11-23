-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditive
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:09.767089+00:00
-- url     : https://prove2.me/theorems/a54a7f3b-d71f-4db6-ad66-3cb820d8c154
-- title:
--   Quadratic Weil Fourier Preserves Test Additive
-- statement:
--   Definitions and structural lemmas for Quadratic Weil Fourier Preserves Test Additive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFourierPreservesTestAdditive.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.WeilQuad.FourierTest
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
theorem star_smul_F (A : Et F E) (c : F) (y : A.L) : star (c • y) = c • star y := by
  rw [Algebra.smul_def, Algebra.smul_def, star_mul, mul_comm, IsScalarTower.algebraMap_apply F A.K A.L, A.star_K]
def beta (A : Et F E) (x : A.K) : LinearMap.BilinForm F A.L :=
  LinearMap.mk₂ F (fun y' y => Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y' * y)))
    (by intro a b c; simp only [star_add, add_mul, map_add, mul_add])
    (by intro c a b
        rw [star_smul_F, smul_mul_assoc, LinearMap.map_smul_of_tower, mul_smul_comm, LinearMap.map_smul])
    (by intro a b c; simp only [mul_add, map_add])
    (by intro c a b
        rw [mul_smul_comm, LinearMap.map_smul_of_tower, mul_smul_comm, LinearMap.map_smul])
end GlobalTheory.JR.WeilQuad.FourierTest



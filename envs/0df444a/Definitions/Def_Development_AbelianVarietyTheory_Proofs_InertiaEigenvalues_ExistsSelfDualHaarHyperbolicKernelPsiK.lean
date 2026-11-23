-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualHaarHyperbolicKernelPsiK
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualHaarHyperbolicKernelPsiK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:54:44.191679+00:00
-- url     : https://prove2.me/theorems/dbd4ddbe-95a8-4b32-8f26-1226c16cbf8f
-- title:
--   Exists Self Dual Haar Hyperbolic Kernel Psi K
-- statement:
--   Definitions and structural lemmas for Exists Self Dual Haar Hyperbolic Kernel Psi K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSelfDualHaarHyperbolicKernelPsiK.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR.Hyp
noncomputable def trxForm {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (x : A.K) : LinearMap.BilinForm F A.K :=
  LinearMap.mk₂ F (fun u b => Algebra.trace F A.K (x * u * b))
    (fun m₁ m₂ n => by simp [mul_add, add_mul])
    (fun c m n => by simp [mul_smul_comm, smul_mul_assoc])
    (fun m n₁ n₂ => by simp [mul_add])
    (fun c m n => by simp [mul_smul_comm, smul_mul_assoc])
end GlobalTheory.JR.Hyp



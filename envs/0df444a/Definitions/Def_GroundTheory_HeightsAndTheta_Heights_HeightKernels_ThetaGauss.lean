-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:48.264061+00:00
-- url     : https://prove2.me/theorems/fb971235-286c-49a3-a8b4-3a8f7d986c38
-- title:
--   Theta Gauss
-- statement:
--   Definitions and structural lemmas for Theta Gauss, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ThetaGauss.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix MeasureTheory Real
open scoped MatrixOrder
namespace GroundTheory.Heights₂.Heights
namespace KTheta
noncomputable section
variable {g : ℕ}
theorem intVec_mem_span (k : Fin g → ℤ) :
    intVec k ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g))) := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  intro i
  exact ⟨k i, by simp [intVec]⟩
theorem exists_int_of_mem_span {x : Fin g → ℝ}
    (hx : x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g)))) (i : Fin g) :
    ∃ n : ℤ, x i = n := by
  rw [Module.Basis.mem_span_iff_repr_mem] at hx
  obtain ⟨n, hn⟩ := hx i
  exact ⟨n, by simpa using hn.symm⟩
def latticeEquiv :
    (Fin g → ℤ) ≃ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g)))).toAddSubgroup where
  toFun k := ⟨intVec k, intVec_mem_span k⟩
  invFun γ := fun i => ⌊(γ : Fin g → ℝ) i⌋
  left_inv k := by funext i; simp [intVec]
  right_inv γ := by
    apply Subtype.ext; funext i
    obtain ⟨n, hn⟩ := exists_int_of_mem_span γ.2 i
    simp [intVec, hn]
end
end KTheta
end GroundTheory.Heights₂.Heights



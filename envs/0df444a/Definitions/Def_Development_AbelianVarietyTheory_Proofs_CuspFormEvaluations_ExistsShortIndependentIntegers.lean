-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsShortIndependentIntegers
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsShortIndependentIntegers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:47.641873+00:00
-- url     : https://prove2.me/theorems/a38a5c9a-6775-45c3-885b-2776b39c6638
-- title:
--   Exists Short Independent Integers
-- statement:
--   Definitions and structural lemmas for Exists Short Independent Integers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsShortIndependentIntegers.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Submodule
open scoped nonZeroDivisors
namespace GlobalTheory
namespace ShortIntegers
section Pairing
variable {V : Type} [AddCommGroup V] [Module ℚ V]
end Pairing
variable {K : Type} [Field K] [NumberField K]
noncomputable def realCoords {M : ℕ} (e : Fin M ≃ (K →+* ℂ)) (ε : ℝ) :
    K →ₗ[ℚ] EuclideanSpace ℝ (Fin M) where
  toFun x := WithLp.toLp 2 fun i => (e i x).re + ε * (e i x).im
  map_add' x y := by
    ext i
    simp
    ring
  map_smul' c x := by
    ext i
    simp [Rat.smul_def]
    ring
end ShortIntegers
end GlobalTheory



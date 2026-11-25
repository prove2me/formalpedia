-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:24:15.641797+00:00
-- url     : https://prove2.me/theorems/a54a88bf-3a1a-4b2d-bb7a-a379c43949e9
-- title:
--   Linear Independent Real Of Int
-- statement:
--   Definitions and structural lemmas for Linear Independent Real Of Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Theta
namespace FunctionalEquationAlt
namespace ShortGen
open Module Submodule Matrix
open scoped RealInnerProductSpace
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
def Sep (L : Submodule ℤ W) (lam : ℝ) : Prop := ∀ x ∈ L, x ≠ 0 → lam ≤ ‖x‖
def proj (v : W) : W →ₗ[ℝ] W where
  toFun x := x - (inner ℝ v x / ‖v‖ ^ 2) • v
  map_add' x y := by rw [inner_add_right, add_div, add_smul]; abel
  map_smul' r x := by
    rw [real_inner_smul_right, RingHom.id_apply, smul_sub, smul_smul, mul_div_assoc]
end
end ShortGen
end FunctionalEquationAlt
end GroundTheory.Heights₂.Theta



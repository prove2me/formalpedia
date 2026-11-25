-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenvectorOfGeneralizedEigenUnramified
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenvectorOfGeneralizedEigenUnramified
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:41.531423+00:00
-- url     : https://prove2.me/theorems/d279e2c6-6e7e-4afd-afb6-bea75cbf321d
-- title:
--   Eigenvector Of Generalized Eigen Unramified
-- statement:
--   Definitions and structural lemmas for Eigenvector Of Generalized Eigen Unramified, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EigenvectorOfGeneralizedEigenUnramified.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators TensorProduct
open Formalism.L2.FormalSeriesBounds
namespace GlobalTheory.GenEigen
variable {C : Type} [Field C] {V : VF C}
theorem ge_mulVec {κ : Type} [Fintype κ] {M : Matrix κ κ C} (hM : ∀ i j, V.Ge 0 (M i j))
    {z : κ → C} {m : ℝ} (hz : ∀ i, V.Ge m (z i)) (i : κ) : V.Ge m (M.mulVec z i) :=
  VF.Ge.sum fun j _ => (hM i j).mul_int (hz j)
def levelIdeal {κ : Type} [Fintype κ] [DecidableEq κ] {B : Type} [CommRing B]
    (Φ : B →+* Matrix κ κ C) (hΦ : ∀ b i j, V.Ge 0 (Φ b i j)) (w : κ → C) (m : ℝ) : Ideal B where
  carrier := {b | ∀ i, V.Ge m ((Φ b).mulVec w i)}
  add_mem' := by
    intro a b ha hb i
    rw [map_add, Matrix.add_mulVec]
    exact (ha i).add (hb i)
  zero_mem' := by
    intro i
    rw [map_zero, Matrix.zero_mulVec]
    exact VF.Ge.zero m
  smul_mem' := by
    intro c b hb i
    rw [smul_eq_mul, map_mul, ← Matrix.mulVec_mulVec]
    exact ge_mulVec (hΦ c) hb i
end GlobalTheory.GenEigen



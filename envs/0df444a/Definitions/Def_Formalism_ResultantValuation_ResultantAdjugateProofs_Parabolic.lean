-- Prove2me | Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Parabolic
-- name    : Formalism_ResultantValuation_ResultantAdjugateProofs_Parabolic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:15:54.010815+00:00
-- url     : https://prove2.me/theorems/1fca1552-7be0-4c86-9777-86e1c56acea5
-- title:
--   Parabolic
-- statement:
--   Definitions and structural lemmas for Parabolic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Parabolic.lean

import Definitions.Def_Formalism_ResultantValuation_SubspaceCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.ResultantValuation
open Module
namespace ParabolicCounting
variable (F : Type) [Field F] (r t : ℕ)
def firstBlock : Submodule F (Fin (r + t) → F) where
  carrier := {v | ∀ i : Fin (r + t), r ≤ (i : ℕ) → v i = 0}
  add_mem' := by
    intro a b ha hb i hi
    simp [ha i hi, hb i hi]
  zero_mem' := by
    intro i _
    rfl
  smul_mem' := by
    intro c v hv i hi
    simp [hv i hi]
@[instance_reducible] def act : MulAction (GL (Fin (r + t)) F) (Submodule F (Fin (r + t) → F)) where
  smul g W := W.map (Matrix.mulVecLin (g : Matrix (Fin (r + t)) (Fin (r + t)) F))
  one_smul W := by
    show W.map _ = W
    rw [Units.val_one, Matrix.mulVecLin_one, Submodule.map_id]
  mul_smul g h W := by
    show W.map _ = (W.map _).map _
    rw [Units.val_mul, Matrix.mulVecLin_mul, Submodule.map_comp]
attribute [local instance] act
def lequiv (g : GL (Fin (r + t)) F) : (Fin (r + t) → F) ≃ₗ[F] (Fin (r + t) → F) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv F _ (Matrix.GeneralLinearGroup.toLin g)
end ParabolicCounting
end Formalism.ResultantValuation



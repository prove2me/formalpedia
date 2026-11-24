-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:12.105486+00:00
-- url     : https://prove2.me/theorems/b138b35d-c144-450d-a857-29b10bd40ca8
-- title:
--   PTrans All A
-- statement:
--   Definitions and structural lemmas for PTrans All A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransAllA.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one


set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
namespace PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {P : Type} [Fintype P] [DecidableEq P]
omit [Fintype P] [DecidableEq P] in
@[simp] theorem liftA_apply (B : Module.End ℂ M) : liftA n M P B = lift B := rfl
def cj {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] W) :
    Module.End ℂ W →ₐ[ℂ] Module.End ℂ V where
  toFun X := e.symm.toLinearMap ∘ₗ X ∘ₗ e.toLinearMap
  map_one' := LinearMap.ext fun v => by simp
  map_mul' X Y := LinearMap.ext fun v => by simp
  map_zero' := LinearMap.ext fun v => by simp
  map_add' X Y := LinearMap.ext fun v => by simp
  commutes' r := LinearMap.ext fun v => by simp
end PositivityTheory.Rg.Cz.TA
end



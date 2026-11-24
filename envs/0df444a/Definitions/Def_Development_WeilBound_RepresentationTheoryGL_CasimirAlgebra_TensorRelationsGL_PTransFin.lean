-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFin
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:05.86107+00:00
-- url     : https://prove2.me/theorems/aaa8d8b8-e193-4853-a2cf-c59da890332d
-- title:
--   PTrans Fin
-- statement:
--   Definitions and structural lemmas for PTrans Fin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTransFin.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinF
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
namespace PositivityTheory.Rg.Cz
namespace TF
def rc {W : Type*} [AddCommGroup W] [Module ℂ W] (A : Module.End ℂ W) : Module.End ℂ (W →ₗ[ℂ] ℂ) where
  toFun f := f ∘ₗ A
  map_add' f f' := LinearMap.add_comp A f' f
  map_smul' c f := LinearMap.smul_comp c f A
def lc {W : Type*} [AddCommGroup W] [Module ℂ W] (ψ : W →ₗ[ℂ] ℂ) : Module.End ℂ W →ₗ[ℂ] (W →ₗ[ℂ] ℂ) where
  toFun r := ψ ∘ₗ r
  map_add' r r' := LinearMap.comp_add r r' ψ
  map_smul' c r := by ext; simp
def ev {W : Type*} [AddCommGroup W] [Module ℂ W] (v : W) : (W →ₗ[ℂ] ℂ) →ₗ[ℂ] ℂ where
  toFun f := f v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end TF
end PositivityTheory.Rg.Cz



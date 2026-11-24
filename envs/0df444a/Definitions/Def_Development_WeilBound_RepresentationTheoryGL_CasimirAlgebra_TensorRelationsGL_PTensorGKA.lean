-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
-- name    : Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:54.38342+00:00
-- url     : https://prove2.me/theorems/ede42234-ca23-4fc1-a631-e52cc11aec63
-- title:
--   PTensor GKA
-- statement:
--   Definitions and structural lemmas for PTensor GKA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/TensorRelationsGL/PTensorGKA.lean

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
namespace PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
def Aop (K : P → Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => ∑ J : P → Fin n, (∏ q, K q (I q) (J q)) • LinearMap.proj J
def mAt (p : P) (A : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => ∑ j, A (I p) j • LinearMap.proj (Function.update I p j)
theorem mAt_apply (p : P) (A : Matrix (Fin n) (Fin n) ℂ) (f : TV n M P) (I : P → Fin n) :
    mAt p A f I = ∑ j, A (I p) j • f (Function.update I p j) := by
  simp only [mAt, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply]
def mAtL (p : P) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (TV n M P) where
  toFun := mAt p
  map_add' A B := by
    refine LinearMap.ext fun f => funext fun I => ?_
    simp only [LinearMap.add_apply, Pi.add_apply, mAt_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    refine LinearMap.ext fun f => funext fun I => ?_
    simp only [LinearMap.smul_apply, Pi.smul_apply, mAt_apply, Matrix.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum, RingHom.id_apply]
end PositivityTheory.Rg.Cz.TGK
end



-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:59:59.071801+00:00
-- url     : https://prove2.me/theorems/dd5b869a-9e8c-40ca-874e-3efd4e88eef2
-- title:
--   Orthogonal Isomorphism Holds
-- statement:
--   Definitions and structural lemmas for Orthogonal Isomorphism Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/OrthogonalIsomorphismHolds.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_add_left__c646ba94555b
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_add_right__407452ae58c2
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_smul_left__f870cf5261a3
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_smul_right__50546d9c35a2
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_zero_left__85aaa0c1d77b
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_PW_fock_zero_right__1016718d7644
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last


set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
section perp
variable {p : ℕ} [Fact p.Prime] {σ : Type}
noncomputable def perpV (h : MvPolynomial σ ℚ_[p]) : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p]) where
  carrier := {x | fock p x h = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [fock_add_left', ha, hb, add_zero]
  zero_mem' := fock_zero_left' h
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [fock_smul_left', hx, mul_zero]
noncomputable def perpS (A : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p]) where
  carrier := {y | ∀ x ∈ A, fock p x y = 0}
  add_mem' := by
    intro a b ha hb x hx
    rw [fock_add_right', ha x hx, hb x hx, add_zero]
  zero_mem' := fun x _ => fock_zero_right' x
  smul_mem' := by
    intro c y hy x hx
    rw [fock_smul_right', hy x hx, mul_zero]
end perp
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
end Formalism.InvariantFactorPaths.PW



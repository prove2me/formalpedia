-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:26:53.156968+00:00
-- url     : https://prove2.me/theorems/09f7a0fa-3ce0-4180-9aef-6e745ee70b6a
-- title:
--   Coe Norm Eq Prod Smul Norm
-- statement:
--   Definitions and structural lemmas for Coe Norm Eq Prod Smul Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/CoeNormEqProdSmulNorm.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Reciprocity
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk


set_option autoImplicit false
namespace GroundTheory.LocalField.Abstract
open ProfiniteInteger
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
namespace ClassFieldData
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
omit [TotallyDisconnectedSpace G] in

instance finiteIndex_inf_ker (d : G →* Multiplicative ℤ̂) (K L : OpenSubgroup G) :
    (((L : Subgroup G) ⊓ d.ker).subgroupOf ((K : Subgroup G) ⊓ d.ker)).FiniteIndex := by
  have h : ((L : Subgroup G) ⊓ d.ker).subgroupOf ((K : Subgroup G) ⊓ d.ker) =
      (L : Subgroup G).subgroupOf ((K : Subgroup G) ⊓ d.ker) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, and_iff_left_iff_imp]
    exact fun _ => x.2.2
  rw [h]
  infer_instance
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K)
end ClassFieldData
end GroundTheory.LocalField.Abstract



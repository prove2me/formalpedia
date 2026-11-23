-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralThird
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralThird
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:52:49.28995+00:00
-- url     : https://prove2.me/theorems/9dbe22e5-dc6c-4b10-9d8c-322092ee1a89
-- title:
--   Cm Type Period Integral Third
-- statement:
--   Definitions and structural lemmas for Cm Type Period Integral Third, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegralThird.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
namespace GlobalTheory.EigenLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H]
def tensAct (ρ : orderC c →+* Module.End O H) : orderC c ⊗[ℤ] O →ₗ[ℤ] Module.End O H :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun (a : orderC c) (x : O) => x • ρ a)
    (fun a b x => by simp [map_add, smul_add])
    (fun n a x => by rw [map_zsmul, smul_comm])
    (fun a x y => by simp [add_smul])
    (fun n a x => smul_assoc n x (ρ a)))
end GlobalTheory.EigenLattice



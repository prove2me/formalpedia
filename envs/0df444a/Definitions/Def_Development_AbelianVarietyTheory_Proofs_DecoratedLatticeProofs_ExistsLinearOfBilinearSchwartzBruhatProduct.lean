-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLinearOfBilinearSchwartzBruhatProduct
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLinearOfBilinearSchwartzBruhatProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:39.556302+00:00
-- url     : https://prove2.me/theorems/f389fe2a-0b28-4640-bdbf-6504eda19de6
-- title:
--   Exists Linear Of Bilinear Schwartz Bruhat Product
-- statement:
--   Definitions and structural lemmas for Exists Linear Of Bilinear Schwartz Bruhat Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLinearOfBilinearSchwartzBruhatProduct.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Theorems.Thm_GlobalTheory_LocFlat_CFac_mulLC_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LocFlat.CFac.mulLC_apply


set_option autoImplicit false
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.LocFlat.CFac
def prodSBBil (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    SB X →ₗ[ℂ] SB Y →ₗ[ℂ] SB (X × Y) :=
  LinearMap.mk₂ ℂ prodSB
    (fun f f' g => by ext p; simp [add_mul])
    (fun c f g => by ext p; simp [mul_assoc])
    (fun f g g' => by ext p; simp [mul_add])
    (fun c f g => by ext p; simp; ring)
def tensorToProd (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    SB X ⊗[ℂ] SB Y →ₗ[ℂ] SB (X × Y) := TensorProduct.lift (prodSBBil X Y)
end GlobalTheory.LocFlat.CFac
namespace GlobalTheory.LocFlat.CFac
end GlobalTheory.LocFlat.CFac



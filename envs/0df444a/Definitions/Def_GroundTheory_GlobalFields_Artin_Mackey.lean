-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
-- name    : GroundTheory_GlobalFields_Artin_Mackey
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:37:41.584359+00:00
-- url     : https://prove2.me/theorems/4d99865c-3b1f-4c0a-a830-e2d958ce6227
-- title:
--   Mackey
-- statement:
--   Definitions and structural lemmas for Mackey, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Mackey.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_TateCohomology_DoubleCosetSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
namespace GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {G : Type*} [Group G]
section ExtendByZero
theorem mem_conj_smul_iff (H : Subgroup G) (a g : G) :
    g ∈ (MulAut.conj a • H : Subgroup G) ↔ a⁻¹ * g * a ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def, MulAut.conj_apply,
    inv_inv]
theorem mem_conj_inv_smul_iff (H : Subgroup G) (x g : G) :
    g ∈ (MulAut.conj x⁻¹ • H : Subgroup G) ↔ x * g * x⁻¹ ∈ H := by
  rw [mem_conj_smul_iff, inv_inv]
open Classical in

def extendByZero (H : Subgroup G) (f : H → ℂ) (g : G) : ℂ :=
  if h : g ∈ H then f ⟨g, h⟩ else 0
end ExtendByZero
section Count
variable [Fintype G]
end Count
section Mackey
def conjFun (H D : Subgroup G) (x : G) (f : H → ℂ) :
    (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D → ℂ :=
  fun d ↦ f ⟨x * ((d : D) : G) * x⁻¹,
    (mem_conj_inv_smul_iff H x _).1 (Subgroup.mem_subgroupOf.1 d.2)⟩
variable [Fintype G]
end Mackey
end GroundTheory.Global.Artin



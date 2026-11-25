-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityTransfer
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:21:37.728948+00:00
-- url     : https://prove2.me/theorems/5b2641db-78fc-5b05-9668-8a572139acd7
-- title:
--   Functoriality Transfer
-- statement:
--   Definitions and structural lemmas for Functoriality Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/FunctorialityTransfer.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_FunctorialityNorm
import Theorems.Thm_GroundTheory_LocalField_Abstract_galRestrict_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField.Abstract
open ProfiniteInteger MulAction
section Transfer
end Transfer
section FixedField
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}
variable [CompactSpace G] [TotallyDisconnectedSpace G]
end FixedField
section Ver
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
  [((L : Subgroup G).subgroupOf K').Normal]
omit [IsTopologicalGroup G] [CompactSpace G] in

theorem galRestrict_injective (hK'K : K' ≤ K) :
    Function.Injective (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [galRestrict_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hq
noncomputable def verlagerung (hK'K : K' ≤ K) :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K →*
      Abelianization ((K' : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K') :=
  ((Abelianization.of).comp
    (MonoidHom.ofInjective (galRestrict_injective (L := L) hK'K)).symm.toMonoidHom).transfer
end Ver
namespace ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A}
section Ver
variable {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
  [((L : Subgroup G).subgroupOf K').Normal]
end Ver
end ClassFieldData
end GroundTheory.LocalField.Abstract



-- Prove2me | Definitions.Def_SharpIntermediateSubgroupBounds_Blocks
-- name    : SharpIntermediateSubgroupBounds_Blocks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:45:36.281881+00:00
-- url     : https://prove2.me/theorems/e748465f-376c-5730-a215-ba31927b3865
-- title:
--   Blocks
-- statement:
--   Definitions and structural lemmas for Blocks, from Sébastien Palcoux (sebastienpalcoux/sharp-intermediate-subgroup-bounds; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sharp bounds for intervals in finite subgroup lattices development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Blocks.lean

import Mathlib.GroupTheory.GroupAction.Blocks
import Definitions.Def_SharpIntermediateSubgroupBounds_GroupMain
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
import Theorems.Thm_SharpIntermediateSubgroupBounds_natFloor_indexLog
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.escapeBranchProduct_cons
attribute [local simp] SharpIntermediateSubgroupBounds.natFloor_indexLog


set_option autoImplicit true
namespace SharpIntermediateSubgroupBounds
open MulAction
open scoped Pointwise
variable (G X : Type*) [Group G] [Fintype G] [Fintype X]
variable [MulAction G X] [MulAction.IsPretransitive G X]
def IsSystemOfImprimitivity (P : Set (Set X)) : Prop :=
  MulAction.IsBlockSystem G P ∧
    ∀ (g : G) (B : Set X), B ∈ P → g • B ∈ P
abbrev SystemOfImprimitivity :=
  {P : Set (Set X) // IsSystemOfImprimitivity G X P}
def pointedBlockToSystemOfImprimitivity (a : X) (B : MulAction.BlockMem G a) :
    SystemOfImprimitivity G X := by
  refine ⟨Set.range fun g : G ↦ g • (B : Set X), ?_, ?_⟩
  · exact B.2.2.isBlockSystem ⟨a, B.2.1⟩
  · rintro g C ⟨h, rfl⟩
    exact ⟨g * h, by simp only [smul_smul]⟩
noncomputable def systemOfImprimitivityToPointedBlock (a : X)
    (P : SystemOfImprimitivity G X) : MulAction.BlockMem G a := by
  let B : Set X := (P.2.1.1.2 a).choose
  have hB : B ∈ P.1 ∧ a ∈ B := (P.2.1.1.2 a).choose_spec.1
  exact ⟨B, hB.2, P.2.1.2 hB.1⟩
lemma systemOfImprimitivityToPointedBlock_mem (a : X)
    (P : SystemOfImprimitivity G X) :
    (systemOfImprimitivityToPointedBlock G X a P : Set X) ∈ P.1 := by
  exact (P.2.1.1.2 a).choose_spec.1.1
noncomputable def pointedBlock_systemOfImprimitivityEquiv (a : X) :
    MulAction.BlockMem G a ≃ SystemOfImprimitivity G X where
  toFun := pointedBlockToSystemOfImprimitivity G X a
  invFun := systemOfImprimitivityToPointedBlock G X a
  left_inv := by
    intro B
    apply Subtype.ext
    let P := pointedBlockToSystemOfImprimitivity G X a B
    exact (P.2.1.1.2 a).unique
      ⟨systemOfImprimitivityToPointedBlock_mem G X a P,
        (systemOfImprimitivityToPointedBlock G X a P).2.1⟩
      ⟨⟨1, by simp⟩, B.2.1⟩
  right_inv := by
    intro P
    apply Subtype.ext
    ext C
    constructor
    · rintro ⟨g, rfl⟩
      exact P.2.2 g _ (systemOfImprimitivityToPointedBlock_mem G X a P)
    · intro hC
      obtain ⟨x, hx⟩ := Setoid.nonempty_of_mem_partition P.2.1.1 hC
      obtain ⟨g, hga⟩ := MulAction.exists_smul_eq G a x
      have hbase :
          (systemOfImprimitivityToPointedBlock G X a P : Set X) ∈ P.1 :=
        systemOfImprimitivityToPointedBlock_mem G X a P
      have hgmem : g • (systemOfImprimitivityToPointedBlock G X a P : Set X) ∈
          P.1 := P.2.2 g _ hbase
      have hxg : x ∈ g • (systemOfImprimitivityToPointedBlock G X a P : Set X) := by
        rw [← hga, Set.smul_mem_smul_set_iff]
        exact (systemOfImprimitivityToPointedBlock G X a P).2.1
      exact ⟨g, Setoid.eq_of_mem_eqv_class P.2.1.1.2 hgmem hxg hC hx⟩
noncomputable local instance blockMemFintype (a : X) :
    Fintype (MulAction.BlockMem G a) :=
  Fintype.ofFinite _
local instance blocksSubgroupFinite : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
noncomputable local instance blocksIntervalFintype (H : Subgroup G) :
    Fintype (Set.Ici H) :=
  Fintype.ofFinite _
noncomputable local instance systemOfImprimitivityFintype :
    Fintype (SystemOfImprimitivity G X) :=
  Fintype.ofFinite _
end SharpIntermediateSubgroupBounds



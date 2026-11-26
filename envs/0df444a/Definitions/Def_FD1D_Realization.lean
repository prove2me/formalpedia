-- Prove2me | Definitions.Def_FD1D_Realization
-- name    : FD1D_Realization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:40:57.241148+00:00
-- url     : https://prove2.me/theorems/1c531db7-b547-4783-a1d2-052e7118e544
-- title:
--   Realization
-- statement:
--   Definitions and structural lemmas for Realization, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Realization.lean

import Definitions.Def_FD1D_Spatial
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_HaarSupportNested_trans
import Theorems.Thm_FD1D_SupplyConfiguration_countState_apply
import Theorems.Thm_FD1D_dyadicCellWidth_pos
import Theorems.Thm_FD1D_dyadicCell_subset_unit
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.SupplyConfiguration.countState_apply
attribute [local simp] FD1D.weightedLevel_zero


set_option autoImplicit true
namespace FD1D
noncomputable section
open Set
namespace SupplyConfiguration
variable {L m : ℕ}
abbrev CountSlot (x : InventoryState (DyadicNode L) m) :=
  Σ i : DyadicNode L, Fin (x.1 i)
noncomputable def countSlotEquiv
    (x : InventoryState (DyadicNode L) m) :
    Fin m ≃ CountSlot x :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_sigma]
    simpa using x.2.symm)
noncomputable def countAssignment
    (x : InventoryState (DyadicNode L) m) (j : Fin m) :
    DyadicNode L :=
  (countSlotEquiv x j).1
def countSlotFiberEquiv
    (x : InventoryState (DyadicNode L) m) (i : DyadicNode L) :
    {s : CountSlot x // s.1 = i} ≃ Fin (x.1 i) where
  toFun s :=
    Fin.cast
      (congrArg (fun k => x.1 k) s.2)
      s.1.2
  invFun k :=
    ⟨⟨i, k⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨k, slot⟩, hki⟩
    dsimp at hki
    subst k
    rfl
  right_inv _ := rfl
noncomputable def countAssignmentFiberSlotEquiv
    (x : InventoryState (DyadicNode L) m) (i : DyadicNode L) :
    ↥(Finset.univ.filter fun j : Fin m => countAssignment x j = i) ≃
      {s : CountSlot x // s.1 = i} where
  toFun j :=
    ⟨countSlotEquiv x j.1, by
      simpa [countAssignment] using (Finset.mem_filter.mp j.2).2⟩
  invFun s :=
    ⟨(countSlotEquiv x).symm s.1, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change (countSlotEquiv x ((countSlotEquiv x).symm s.1)).1 = i
      rw [Equiv.apply_symm_apply]
      exact s.2⟩
  left_inv j := by
    apply Subtype.ext
    exact (countSlotEquiv x).symm_apply_apply j.1
  right_inv s := by
    apply Subtype.ext
    exact (countSlotEquiv x).apply_symm_apply s.1
noncomputable def countAssignmentFiberEquiv
    (x : InventoryState (DyadicNode L) m) (i : DyadicNode L) :
    ↥(Finset.univ.filter fun j : Fin m => countAssignment x j = i) ≃
      Fin (x.1 i) :=
  (countAssignmentFiberSlotEquiv x i).trans (countSlotFiberEquiv x i)
noncomputable def ofCountState
    (x : InventoryState (DyadicNode L) m) :
    SupplyConfiguration L m where
  location j := dyadicCellLeft (countAssignment x j)
  leaf j := countAssignment x j
  location_mem_unit j :=
    dyadicCell_subset_unit (countAssignment x j) (by
      exact ⟨le_rfl, le_add_of_nonneg_right (dyadicCellWidth_pos L).le⟩)
  location_mem_cell j :=
    ⟨le_rfl, le_add_of_nonneg_right (dyadicCellWidth_pos L).le⟩
def canonicalFallback (hm : 0 < m) : Fin m :=
  ⟨0, hm⟩
end SupplyConfiguration
end
end FD1D



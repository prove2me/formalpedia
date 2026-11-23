-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
-- name    : GroundTheory_AutomorphicForms_InductionParabolicGroups
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:16.751296+00:00
-- url     : https://prove2.me/theorems/acb7fe07-f9ed-4f26-9f60-749612a18476
-- title:
--   Induction Parabolic Groups
-- statement:
--   Definitions and structural lemmas for Induction Parabolic Groups, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk


set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa
variable (F : Type*) [Field F] (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
def blockDiagPart (A : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => if β i = β j then A i j else 0
variable {F n β}
theorem blockDiagPart_apply (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    blockDiagPart F n β A i j = if β i = β j then A i j else 0 := rfl
theorem blockDiagPart_one : blockDiagPart F n β 1 = 1 := by
  ext i j
  rw [blockDiagPart_apply]
  split_ifs with h
  · rfl
  · rw [one_apply_ne fun hij => h (by rw [hij])]
theorem blockDiagPart_mul {A B : Matrix (Fin n) (Fin n) F} (hA : A.BlockTriangular β)
    (hB : B.BlockTriangular β) :
    blockDiagPart F n β (A * B) = blockDiagPart F n β A * blockDiagPart F n β B := by
  ext i j
  simp only [blockDiagPart_apply, mul_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : β i = β k
    · rw [if_pos hk, if_pos (hk.symm.trans h)]
    · rw [if_neg hk, zero_mul]
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · rw [hB (h ▸ hlt : β j < β k), mul_zero]
      · rw [hA hlt, zero_mul]
  · refine (Finset.sum_eq_zero fun k _ => ?_).symm
    by_cases hk : β i = β k
    · rw [if_neg fun h' => h (hk.trans h'), mul_zero]
    · rw [if_neg hk, zero_mul]
variable (F n β)
def levi : Subgroup (GL (Fin n) F) :=
  blockUpper F n β ⊓ blockUpper F n (OrderDual.toDual ∘ β)
variable {F n β}
theorem mem_levi {g : GL (Fin n) F} :
    g ∈ levi F n β ↔ ∀ i j, β i ≠ β j → g i j = 0 := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact h2 (show OrderDual.toDual (β j) < OrderDual.toDual (β i) from h)
    · exact h1 h
  · intro h
    exact ⟨fun i j hij => h i j hij.ne', fun i j hij => h i j
      (show β i < β j from hij).ne⟩
theorem levi_le_blockUpper : levi F n β ≤ blockUpper F n β := inf_le_left
def leviProjFun (p : blockUpper F n β) : GL (Fin n) F where
  val := blockDiagPart F n β (p : GL (Fin n) F)
  inv := blockDiagPart F n β ((p⁻¹ : blockUpper F n β) : GL (Fin n) F)
  val_inv := by
    rw [← blockDiagPart_mul p.2 (p⁻¹).2, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, Units.val_one, blockDiagPart_one]
  inv_val := by
    rw [← blockDiagPart_mul (p⁻¹).2 p.2, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, Units.val_one, blockDiagPart_one]
theorem leviProjFun_mem (p : blockUpper F n β) : leviProjFun p ∈ levi F n β := by
  rw [mem_levi]
  intro i j hij
  show blockDiagPart F n β _ i j = 0
  rw [blockDiagPart_apply, if_neg hij]
variable (F n β)
def leviProj : blockUpper F n β →* levi F n β where
  toFun p := ⟨leviProjFun p, leviProjFun_mem p⟩
  map_one' := Subtype.ext (Units.ext (by
    show blockDiagPart F n β ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1
    rw [Units.val_one, blockDiagPart_one]))
  map_mul' p q := Subtype.ext (Units.ext (by
    show blockDiagPart F n β (((p * q : blockUpper F n β) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = blockDiagPart F n β (p : GL (Fin n) F) *
        blockDiagPart F n β (q : GL (Fin n) F)
    rw [Subgroup.coe_mul, Units.val_mul, blockDiagPart_mul p.2 q.2]))
variable {F n β}
def leviIncl : levi F n β →* blockUpper F n β :=
  Subgroup.inclusion levi_le_blockUpper
variable (F n β)
def unipotentRadical : Subgroup (GL (Fin n) F) :=
  (leviProj F n β).ker.map (blockUpper F n β).subtype
def oppositeUnipotentRadical : Subgroup (GL (Fin n) F) :=
  unipotentRadical F n (OrderDual.toDual ∘ β)
variable {F n β}
variable (β) in

def blockRank (i : Fin n) : ℕ := (Finset.univ.filter fun j => β j < β i).card
end Parabolic
end GroundTheory.Automorphic



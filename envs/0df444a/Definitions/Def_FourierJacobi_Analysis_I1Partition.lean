-- Prove2me | Definitions.Def_FourierJacobi_Analysis_I1Partition
-- name    : FourierJacobi_Analysis_I1Partition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:24:21.662828+00:00
-- url     : https://prove2.me/theorems/2ca4a9ee-da67-4f61-b7b3-d3f0237666d1
-- title:
--   I1 Partition
-- statement:
--   Definitions and structural lemmas for I1 Partition, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Partition.lean

import Definitions.Def_FourierJacobi_Analysis_I1Complete
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_i1r10Equiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i1r10Equiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero


set_option autoImplicit false
namespace FourierJacobi.Analysis
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
def i1CellIndex (p : LatticeIndex) : Fin 17 :=
  let k := p.1; let j := p.2.1; let h := p.2.2.1; let c := p.2.2.2
  if 1 ≤ k then
    if -2*k ≤ j then
      if -k ≤ h then 0 else 1
    else if h < k+j then 7
    else if j ≤ 2*h then
      if j % 2 = 0 then 2 else 3
    else if 2*h = j-1 then
      if c = 0 then 4 else 5
    else 6
  else if 0 ≤ j then
    if h < 0 then 10
    else if k = 0 then 8 else 9
  else if h < j then 16
  else if j ≤ 2*h then
    if j % 2 = 0 then 11 else 12
  else if 2*h = j-1 then
    if c = 0 then 13 else 14
  else 15
abbrev I1Cell (i : Fin 17) := {p : LatticeIndex // i1CellIndex p = i}
def i1PartitionEquiv : (Σ i : Fin 17, I1Cell i) ≃ LatticeIndex :=
  Equiv.sigmaFiberEquiv i1CellIndex
@[simp] theorem i1PartitionEquiv_val (p : Σ i : Fin 17, I1Cell i) :
    i1PartitionEquiv p = p.2.val := rfl
theorem i1r1_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 0 ↔ (1 ≤ k ∧ -2 * k ≤ j ∧ -k ≤ h) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r1DepthEquiv : (I1R1Row × ℕ) ≃ I1Cell 0 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r1_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r1_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r1_cell_iff k j h c).mp hp
    rfl
@[simp] theorem i1r1DepthEquiv_val (p : I1R1Row × ℕ) :
    (i1r1DepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl
theorem i1r2_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 1 ↔ (1 ≤ k ∧ -2 * k ≤ j ∧ h < -k) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r2DepthEquiv : (I1R2Row × ℕ) ≃ I1Cell 1 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r2_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r2_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r2_cell_iff k j h c).mp hp
    rfl
@[simp] theorem i1r2DepthEquiv_val (p : I1R2Row × ℕ) :
    (i1r2DepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl
theorem i1r3ae_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 2 ↔ (1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 0) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r3aeDepthEquiv : (I1R3AERow × ℕ) ≃ I1Cell 2 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r3ae_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r3ae_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r3ae_cell_iff k j h c).mp hp
    rfl
@[simp] theorem i1r3aeDepthEquiv_val (p : I1R3AERow × ℕ) :
    (i1r3aeDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl
theorem i1r3ao_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 3 ↔ (1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 1) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r3aoDepthEquiv : (I1R3AORow × ℕ) ≃ I1Cell 3 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r3ao_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r3ao_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r3ao_cell_iff k j h c).mp hp
    rfl
@[simp] theorem i1r3aoDepthEquiv_val (p : I1R3AORow × ℕ) :
    (i1r3aoDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl
theorem i1r3b_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 4 ↔ (1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-1) ∧ c = 0 := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r3bDepthEquiv : (I1R3BRow) ≃ I1Cell 4 where
  toFun p := ⟨(p.val.1,p.val.2.1,p.val.2.2,0), by
    apply (i1r3b_cell_iff _ _ _ _).mpr
    exact ⟨p.property, by omega⟩⟩
  invFun p := ⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r3b_cell_iff _ _ _ _).mp p.property
    exact hp.1⟩
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r3b_cell_iff k j h c).mp hp
    change (k,j,h,0) = (k,j,h,c)
    exact congrArg (fun z : ℕ => (k,j,h,z)) hh.2.symm
@[simp] theorem i1r3bDepthEquiv_val (p : I1R3BRow) :
    (i1r3bDepthEquiv p).val = (p.val.1,p.val.2.1,p.val.2.2,0) := rfl
theorem i1r3c_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 5 ↔ (1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-1) ∧ 1 ≤ c := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r3cDepthEquiv : (I1R3CRow × ℕ) ≃ I1Cell 5 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2 + 1), by
    apply (i1r3c_cell_iff _ _ _ _).mpr
    exact ⟨p.1.property, by omega⟩⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r3c_cell_iff _ _ _ _).mp p.property
    exact hp.1⟩, p.val.2.2.2 - 1)
  left_inv p := by
    rcases p with ⟨p,c⟩
    simp
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r3c_cell_iff k j h c).mp hp
    change (k,j,h,c-1+1) = (k,j,h,c)
    exact congrArg (fun z : ℕ => (k,j,h,z)) (Nat.sub_add_cancel hh.2)
@[simp] theorem i1r3cDepthEquiv_val (p : I1R3CRow × ℕ) :
    (i1r3cDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2 + 1) := rfl
theorem i1r4_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 6 ↔ (1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h ≤ j-2) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r4DepthEquiv : (I1R4Row × ℕ) ≃ I1Cell 6 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r4_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r4_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r4_cell_iff k j h c).mp hp
    rfl
@[simp] theorem i1r4DepthEquiv_val (p : I1R4Row × ℕ) :
    (i1r4DepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl
theorem i1r5_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 7 ↔ (1 ≤ k ∧ j < -2*k ∧ h < k+j) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r5DepthEquiv : (I1R5Row × ℕ) ≃ I1Cell 7 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r5_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r5_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r5_cell_iff k j h c).mp hp
    rfl
@[simp] theorem i1r5DepthEquiv_val (p : I1R5Row × ℕ) :
    (i1r5DepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl
theorem i1r6a_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 8 ↔ (k = 0 ∧ 0 ≤ j ∧ 0 ≤ h) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r6aDepthEquiv : (I1R6ARow × ℕ) ≃ I1Cell 8 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r6a_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r6a_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r6a_cell_iff k j h c).mp hp
    rfl
@[simp] theorem i1r6aDepthEquiv_val (p : I1R6ARow × ℕ) :
    (i1r6aDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl
theorem i1r6b_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 9 ↔ (k ≤ -1 ∧ 0 ≤ j ∧ 0 ≤ h) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r6bDepthEquiv : (I1R6BRow × ℕ) ≃ I1Cell 9 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r6b_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r6b_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r6b_cell_iff k j h c).mp hp
    rfl
@[simp] theorem i1r6bDepthEquiv_val (p : I1R6BRow × ℕ) :
    (i1r6bDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl
theorem i1r7_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 10 ↔ (k ≤ 0 ∧ 0 ≤ j ∧ h < 0) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r7DepthEquiv : (I1R7Row × ℕ) ≃ I1Cell 10 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r7_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r7_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r7_cell_iff k j h c).mp hp
    rfl
@[simp] theorem i1r7DepthEquiv_val (p : I1R7Row × ℕ) :
    (i1r7DepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl
theorem i1r8ae_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 11 ↔ (k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 0) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r8aeDepthEquiv : (I1R8AERow × ℕ) ≃ I1Cell 11 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r8ae_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r8ae_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r8ae_cell_iff k j h c).mp hp
    rfl
@[simp] theorem i1r8aeDepthEquiv_val (p : I1R8AERow × ℕ) :
    (i1r8aeDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl
theorem i1r8ao_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 12 ↔ (k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 1) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r8aoDepthEquiv : (I1R8AORow × ℕ) ≃ I1Cell 12 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r8ao_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r8ao_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r8ao_cell_iff k j h c).mp hp
    rfl
@[simp] theorem i1r8aoDepthEquiv_val (p : I1R8AORow × ℕ) :
    (i1r8aoDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl
theorem i1r8b_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 13 ↔ (k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h = j-1) ∧ c = 0 := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r8bDepthEquiv : (I1R8BRow) ≃ I1Cell 13 where
  toFun p := ⟨(p.val.1,p.val.2.1,p.val.2.2,0), by
    apply (i1r8b_cell_iff _ _ _ _).mpr
    exact ⟨p.property, by omega⟩⟩
  invFun p := ⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r8b_cell_iff _ _ _ _).mp p.property
    exact hp.1⟩
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r8b_cell_iff k j h c).mp hp
    change (k,j,h,0) = (k,j,h,c)
    exact congrArg (fun z : ℕ => (k,j,h,z)) hh.2.symm
@[simp] theorem i1r8bDepthEquiv_val (p : I1R8BRow) :
    (i1r8bDepthEquiv p).val = (p.val.1,p.val.2.1,p.val.2.2,0) := rfl
theorem i1r8c_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 14 ↔ (k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h = j-1) ∧ 1 ≤ c := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r8cDepthEquiv : (I1R8CRow × ℕ) ≃ I1Cell 14 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2 + 1), by
    apply (i1r8c_cell_iff _ _ _ _).mpr
    exact ⟨p.1.property, by omega⟩⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r8c_cell_iff _ _ _ _).mp p.property
    exact hp.1⟩, p.val.2.2.2 - 1)
  left_inv p := by
    rcases p with ⟨p,c⟩
    simp
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r8c_cell_iff k j h c).mp hp
    change (k,j,h,c-1+1) = (k,j,h,c)
    exact congrArg (fun z : ℕ => (k,j,h,z)) (Nat.sub_add_cancel hh.2)
@[simp] theorem i1r8cDepthEquiv_val (p : I1R8CRow × ℕ) :
    (i1r8cDepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2 + 1) := rfl
theorem i1r9_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 15 ↔ (k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h ≤ j-2) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r9DepthEquiv : (I1R9Row × ℕ) ≃ I1Cell 15 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r9_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r9_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r9_cell_iff k j h c).mp hp
    rfl
@[simp] theorem i1r9DepthEquiv_val (p : I1R9Row × ℕ) :
    (i1r9DepthEquiv p).val = (p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2) := rfl
theorem i1r10_cell_iff (k j h : ℤ) (c : ℕ) :
    i1CellIndex (k,j,h,c) = 16 ↔ (k ≤ 0 ∧ j < 0 ∧ h < j) := by
  unfold i1CellIndex
  dsimp
  split_ifs <;> norm_num <;> omega
def i1r10DepthEquiv : (I1R10Row × ℕ) ≃ I1Cell 16 where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2), by
    apply (i1r10_cell_iff _ _ _ _).mpr
    exact p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1), by
    have hp := (i1r10_cell_iff _ _ _ _).mp p.property
    exact hp⟩, p.val.2.2.2)
  left_inv p := by
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    apply Subtype.ext
    have hh := (i1r10_cell_iff k j h c).mp hp
    rfl
end FourierJacobi.Analysis



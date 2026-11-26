-- Prove2me | Definitions.Def_FourierJacobi_Analysis_I1Complete
-- name    : FourierJacobi_Analysis_I1Complete
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:20:52.203865+00:00
-- url     : https://prove2.me/theorems/dc0ba369-4a8b-5cf5-906d-143fd331ec2e
-- title:
--   I1 Complete
-- statement:
--   Definitions and structural lemmas for I1 Complete, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I1Complete.lean

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero


set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
def i1Raw (t d U V T : ℂ) (p : ℤ × ℤ × ℤ) (c : ℕ) : ℂ :=
  let ell := (cartanIndices 1 p.1 p.2.1 p.2.2 c).1
  let b := (cartanIndices 1 p.1 p.2.1 p.2.2 c).2
  (1 - t ^ 2) ^ 3 * d ^ p.1 *
    t ^ (3 * p.1 + 2 * p.2.1 + 2 * p.2.2 + 3 * ell + 4 * b - 2) *
    (T * U) ^ (ell / 2) * (T * V) ^ b
abbrev I1R1Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ -2 * k ≤ j ∧ -k ≤ h}
def i1r1Equiv : (ℕ × ℕ × ℕ) ≃ I1R1Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ) + 1, (b : ℤ) - 2 * (a : ℤ) - 2, (c : ℤ) - (a : ℤ) - 1)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k - 1).toNat, ( j + 2 * k).toNat, ( h + k).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r1Equiv_val (a b c : ℕ) :
    (i1r1Equiv (a,b,c)).val = ((a : ℤ) + 1, (b : ℤ) - 2 * (a : ℤ) - 2, (c : ℤ) - (a : ℤ) - 1) := rfl
abbrev I1R2Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ -2 * k ≤ j ∧ h < -k}
def i1r2Equiv : (ℕ × ℕ × ℕ) ≃ I1R2Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ) + 1, (b : ℤ) - 2 * (a : ℤ) - 2, -(a : ℤ) - (c : ℤ) - 2)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k - 1).toNat, ( j + 2 * k).toNat, ( -h - k - 1).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r2Equiv_val (a b c : ℕ) :
    (i1r2Equiv (a,b,c)).val = ((a : ℤ) + 1, (b : ℤ) - 2 * (a : ℤ) - 2, -(a : ℤ) - (c : ℤ) - 2) := rfl
abbrev I1R3AERow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 0}
def i1r3aeEquiv : (ℕ × ℕ × ℕ) ≃ I1R3AERow where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-4,-(a : ℤ)-(b : ℤ)-2+(c : ℤ))), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, ((-j-2*k-2)/2).toNat, (h-j/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r3aeEquiv_val (a b c : ℕ) :
    (i1r3aeEquiv (a,b,c)).val = ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-4,-(a : ℤ)-(b : ℤ)-2+(c : ℤ)) := rfl
abbrev I1R3AORow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 1}
def i1r3aoEquiv : (ℕ × ℕ × ℕ) ≃ I1R3AORow where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-1+(c : ℤ))), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, ((-j-2*k-1)/2).toNat, (h-(j+1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r3aoEquiv_val (a b c : ℕ) :
    (i1r3aoEquiv (a,b,c)).val = ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-1+(c : ℤ)) := rfl
abbrev I1R3BRow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-1}
def i1r3bEquiv : (ℕ × ℕ) ≃ I1R3BRow where
  toFun n := ⟨(by
    rcases n with ⟨a, b⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-2)), by
      rcases n with ⟨a, b⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, ((-j-2*k-1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r3bEquiv_val (a b : ℕ) :
    (i1r3bEquiv (a,b)).val = ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-2) := rfl
abbrev I1R3CRow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-1}
def i1r3cEquiv : (ℕ × ℕ) ≃ I1R3CRow where
  toFun n := ⟨(by
    rcases n with ⟨a, b⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-2)), by
      rcases n with ⟨a, b⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, ((-j-2*k-1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r3cEquiv_val (a b : ℕ) :
    (i1r3cEquiv (a,b)).val = ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-2) := rfl
abbrev I1R4Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h ≤ j-2}
def i1r4Equiv : (ℕ × ℕ × ℕ) ≃ I1R4Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4,-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, (h-k-j).toNat, (j-2*h-2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r4Equiv_val (a b c : ℕ) :
    (i1r4Equiv (a,b,c)).val = ((a : ℤ)+1,-2*(a : ℤ)-2*(b : ℤ)-(c : ℤ)-4,-(a : ℤ)-(b : ℤ)-(c : ℤ)-3) := rfl
abbrev I1R5Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; 1 ≤ k ∧ j < -2*k ∧ h < k+j}
def i1r5Equiv : (ℕ × ℕ × ℕ) ≃ I1R5Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact ((a : ℤ)+1,-2*(a : ℤ)-(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-(c : ℤ)-3)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((k-1).toNat, (-j-2*k-1).toNat, (k+j-h-1).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r5Equiv_val (a b c : ℕ) :
    (i1r5Equiv (a,b,c)).val = ((a : ℤ)+1,-2*(a : ℤ)-(b : ℤ)-3,-(a : ℤ)-(b : ℤ)-(c : ℤ)-3) := rfl
abbrev I1R6ARow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k = 0 ∧ 0 ≤ j ∧ 0 ≤ h}
def i1r6aEquiv : (ℕ × ℕ) ≃ I1R6ARow where
  toFun n := ⟨(by
    rcases n with ⟨a, b⟩
    exact (0,(a : ℤ),(b : ℤ))), by
      rcases n with ⟨a, b⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((j).toNat, (h).toNat))
  left_inv n := by
    rcases n with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r6aEquiv_val (a b : ℕ) :
    (i1r6aEquiv (a,b)).val = (0,(a : ℤ),(b : ℤ)) := rfl
abbrev I1R6BRow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ -1 ∧ 0 ≤ j ∧ 0 ≤ h}
def i1r6bEquiv : (ℕ × ℕ × ℕ) ≃ I1R6BRow where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ)-1,(b : ℤ),(c : ℤ))), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k-1).toNat, (j).toNat, (h).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r6bEquiv_val (a b c : ℕ) :
    (i1r6bEquiv (a,b,c)).val = (-(a : ℤ)-1,(b : ℤ),(c : ℤ)) := rfl
abbrev I1R7Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ 0 ≤ j ∧ h < 0}
def i1r7Equiv : (ℕ × ℕ × ℕ) ≃ I1R7Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ),(b : ℤ),-(c : ℤ)-1)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, (j).toNat, (-h-1).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r7Equiv_val (a b c : ℕ) :
    (i1r7Equiv (a,b,c)).val = (-(a : ℤ),(b : ℤ),-(c : ℤ)-1) := rfl
abbrev I1R8AERow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 0}
def i1r8aeEquiv : (ℕ × ℕ × ℕ) ≃ I1R8AERow where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ),-2*(b : ℤ)-2,-(b : ℤ)-1+(c : ℤ))), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, ((-j-2)/2).toNat, (h-j/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r8aeEquiv_val (a b c : ℕ) :
    (i1r8aeEquiv (a,b,c)).val = (-(a : ℤ),-2*(b : ℤ)-2,-(b : ℤ)-1+(c : ℤ)) := rfl
abbrev I1R8AORow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ j ≤ 2*h ∧ j % 2 = 1}
def i1r8aoEquiv : (ℕ × ℕ × ℕ) ≃ I1R8AORow where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)+(c : ℤ))), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, ((-j-1)/2).toNat, (h-(j+1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r8aoEquiv_val (a b c : ℕ) :
    (i1r8aoEquiv (a,b,c)).val = (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)+(c : ℤ)) := rfl
abbrev I1R8BRow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h = j-1}
def i1r8bEquiv : (ℕ × ℕ) ≃ I1R8BRow where
  toFun n := ⟨(by
    rcases n with ⟨a, b⟩
    exact (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)-1)), by
      rcases n with ⟨a, b⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, ((-j-1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r8bEquiv_val (a b : ℕ) :
    (i1r8bEquiv (a,b)).val = (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)-1) := rfl
abbrev I1R8CRow := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h = j-1}
def i1r8cEquiv : (ℕ × ℕ) ≃ I1R8CRow where
  toFun n := ⟨(by
    rcases n with ⟨a, b⟩
    exact (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)-1)), by
      rcases n with ⟨a, b⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, ((-j-1)/2).toNat))
  left_inv n := by
    rcases n with ⟨a, b⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r8cEquiv_val (a b : ℕ) :
    (i1r8cEquiv (a,b)).val = (-(a : ℤ),-2*(b : ℤ)-1,-(b : ℤ)-1) := rfl
abbrev I1R9Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ j ≤ h ∧ 2*h ≤ j-2}
def i1r9Equiv : (ℕ × ℕ × ℕ) ≃ I1R9Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ),-2*(b : ℤ)-(c : ℤ)-2,-(b : ℤ)-(c : ℤ)-2)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, (h-j).toNat, (j-2*h-2).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
@[simp] theorem i1r9Equiv_val (a b c : ℕ) :
    (i1r9Equiv (a,b,c)).val = (-(a : ℤ),-2*(b : ℤ)-(c : ℤ)-2,-(b : ℤ)-(c : ℤ)-2) := rfl
abbrev I1R10Row := {p : ℤ × ℤ × ℤ //
  let k := p.1; let j := p.2.1; let h := p.2.2; k ≤ 0 ∧ j < 0 ∧ h < j}
def i1r10Equiv : (ℕ × ℕ × ℕ) ≃ I1R10Row where
  toFun n := ⟨(by
    rcases n with ⟨a, b, c⟩
    exact (-(a : ℤ),-(b : ℤ)-1,-(b : ℤ)-(c : ℤ)-2)), by
      rcases n with ⟨a, b, c⟩
      dsimp
      omega⟩
  invFun p := (by
    let k := p.val.1; let j := p.val.2.1; let h := p.val.2.2
    exact ((-k).toNat, (-j-1).toNat, (j-h-1).toNat))
  left_inv n := by
    rcases n with ⟨a, b, c⟩
    simp only [Prod.mk.injEq]
    try dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩,hp⟩
    dsimp at hp ⊢
    simp only [Prod.mk.injEq]
    omega
end FourierJacobi.Analysis



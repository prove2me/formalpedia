-- Prove2me | Definitions.Def_FourierJacobi_Analysis_I2Domains
-- name    : FourierJacobi_Analysis_I2Domains
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:54:31.479488+00:00
-- url     : https://prove2.me/theorems/aede0957-9e29-4d1a-a85f-43a0db9e155c
-- title:
--   I2 Domains
-- statement:
--   Definitions and structural lemmas for I2 Domains, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Domains.lean

import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Tactic.FinCases
set_option autoImplicit false
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def i2SpatialPredicate (ν : Fin 25) (p : ℤ × ℤ × ℤ) : Prop :=
  let k := p.1
  let j := p.2.1
  let h := p.2.2
  match ν.val with
  | 0 => 2 ≤ k ∧ -2*k ≤ j ∧ -k ≤ h
  | 1 => k = 1 ∧ -2 ≤ j ∧ -1 ≤ h
  | 2 => 1 ≤ k ∧ -2*k ≤ j ∧ h < -k
  | 3 => 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j-1 ≤ 2*h
  | 4 => 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-2
  | 5 => 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-2
  | 6 => 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-2
  | 7 => 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h ≤ j-3
  | 8 => 1 ≤ k ∧ j < -2*k ∧ h < k+j
  | 9 => k = 0 ∧ 0 ≤ j ∧ -1 ≤ h
  | 10 => k = 0 ∧ j = -1 ∧ -1 ≤ h
  | 11 => k = 0 ∧ -1 ≤ j ∧ h ≤ -2
  | 12 => k = -1 ∧ 0 ≤ j ∧ 0 ≤ h
  | 13 => k = -1 ∧ j = -1 ∧ -1 ≤ h
  | 14 => k = -1 ∧ j = -1 ∧ h ≤ -2
  | 15 => k ≤ -2 ∧ 0 ≤ j ∧ 0 ≤ h
  | 16 => k ≤ -2 ∧ j = -1 ∧ -1 ≤ h
  | 17 => k ≤ -2 ∧ j = -1 ∧ h ≤ -2
  | 18 => k ≤ -1 ∧ 0 ≤ j ∧ h ≤ -1
  | 19 => k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ j-1 ≤ 2*h
  | 20 => k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h = j-2
  | 21 => k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h = j-2
  | 22 => k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h = j-2
  | 23 => k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h ≤ j-3
  | _ => k ≤ 0 ∧ j < -1 ∧ h < j
def i2DepthPredicate (ν : Fin 25) (c : ℕ) : Prop :=
  match ν.val with
  | 4 => c = 0
  | 5 => c = 1
  | 6 => 2 ≤ c
  | 20 => c = 0
  | 21 => c = 1
  | 22 => 2 ≤ c
  | _ => True
abbrev I2SpatialRow (ν : Fin 25) := {p : ℤ × ℤ × ℤ // i2SpatialPredicate ν p}
def i2Case1aEquiv : (ℕ × ℕ × ℕ) ≃ I2SpatialRow 0 where
  toFun n := ⟨((n.1 : ℤ)+2, (n.2.1 : ℤ)-2*((n.1 : ℤ)+2), (n.2.2 : ℤ)-((n.1 : ℤ)+2)), by change 2 ≤ ((n.1 : ℤ)+2) ∧ -2*((n.1 : ℤ)+2) ≤ ((n.2.1 : ℤ)-2*((n.1 : ℤ)+2)) ∧ -((n.1 : ℤ)+2) ≤ ((n.2.2 : ℤ)-((n.1 : ℤ)+2)); omega⟩
  invFun p := ((p.val.1-2).toNat, (p.val.2.1+2*p.val.1).toNat, (p.val.2.2+p.val.1).toNat)
  left_inv n := by
    rcases n with ⟨a,b,c⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change 2 ≤ k ∧ -2*k ≤ j ∧ -k ≤ h at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case1aEquiv_val (n : ℕ × ℕ × ℕ) :
    (i2Case1aEquiv n).val = ((n.1 : ℤ)+2, (n.2.1 : ℤ)-2*((n.1 : ℤ)+2), (n.2.2 : ℤ)-((n.1 : ℤ)+2)) := rfl
def i2Case1bEquiv : (ℕ × ℕ) ≃ I2SpatialRow 1 where
  toFun n := ⟨(1, (n.1 : ℤ)-2, (n.2 : ℤ)-1), by change (1) = 1 ∧ -2 ≤ ((n.1 : ℤ)-2) ∧ -1 ≤ ((n.2 : ℤ)-1); omega⟩
  invFun p := ((p.val.2.1+2).toNat, (p.val.2.2+1).toNat)
  left_inv n := by
    rcases n with ⟨a,b⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k = 1 ∧ -2 ≤ j ∧ -1 ≤ h at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case1bEquiv_val (n : ℕ × ℕ) :
    (i2Case1bEquiv n).val = (1, (n.1 : ℤ)-2, (n.2 : ℤ)-1) := rfl
def i2Case2Equiv : (ℕ × ℕ × ℕ) ≃ I2SpatialRow 2 where
  toFun n := ⟨((n.1 : ℤ)+1, (n.2.1 : ℤ)-2*((n.1 : ℤ)+1), -((n.1 : ℤ)+1)-(n.2.2 : ℤ)-1), by change 1 ≤ ((n.1 : ℤ)+1) ∧ -2*((n.1 : ℤ)+1) ≤ ((n.2.1 : ℤ)-2*((n.1 : ℤ)+1)) ∧ (-((n.1 : ℤ)+1)-(n.2.2 : ℤ)-1) < -((n.1 : ℤ)+1); omega⟩
  invFun p := ((p.val.1-1).toNat, (p.val.2.1+2*p.val.1).toNat, (-p.val.1-p.val.2.2-1).toNat)
  left_inv n := by
    rcases n with ⟨a,b,c⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change 1 ≤ k ∧ -2*k ≤ j ∧ h < -k at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case2Equiv_val (n : ℕ × ℕ × ℕ) :
    (i2Case2Equiv n).val = ((n.1 : ℤ)+1, (n.2.1 : ℤ)-2*((n.1 : ℤ)+1), -((n.1 : ℤ)+1)-(n.2.2 : ℤ)-1) := rfl
def i2Case3aEquiv : (Fin 2 × ℕ × ℕ × ℕ) ≃ I2SpatialRow 3 where
  toFun n := ⟨((n.2.1 : ℤ)+1, -2*((n.2.1 : ℤ)+1)-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1, -((n.2.1 : ℤ)+1)-(n.2.2.1 : ℤ)-1+(n.2.2.2 : ℤ)), by change 1 ≤ ((n.2.1 : ℤ)+1) ∧ (-2*((n.2.1 : ℤ)+1)-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1) < -2*((n.2.1 : ℤ)+1) ∧ ((n.2.1 : ℤ)+1)+(-2*((n.2.1 : ℤ)+1)-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1) ≤ (-((n.2.1 : ℤ)+1)-(n.2.2.1 : ℤ)-1+(n.2.2.2 : ℤ)) ∧ (-2*((n.2.1 : ℤ)+1)-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1)-1 ≤ 2*(-((n.2.1 : ℤ)+1)-(n.2.2.1 : ℤ)-1+(n.2.2.2 : ℤ)); omega⟩
  invFun p := (⟨((-p.val.2.1-2*p.val.1-1)%2).toNat, by omega⟩, (p.val.1-1).toNat, ((-p.val.2.1-2*p.val.1-1)/2).toNat, (p.val.2.2+p.val.1+((-p.val.2.1-2*p.val.1-1)/2)+1).toNat)
  left_inv n := by
    rcases n with ⟨⟨e,he⟩,a,b,c⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ j-1 ≤ 2*h at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case3aEquiv_val (n : Fin 2 × ℕ × ℕ × ℕ) :
    (i2Case3aEquiv n).val = ((n.2.1 : ℤ)+1, -2*((n.2.1 : ℤ)+1)-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1, -((n.2.1 : ℤ)+1)-(n.2.2.1 : ℤ)-1+(n.2.2.2 : ℤ)) := rfl
def i2Case3bEquiv : (ℕ × ℕ) ≃ I2SpatialRow 4 where
  toFun n := ⟨((n.1 : ℤ)+1, -2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2, -((n.1 : ℤ)+1)-(n.2 : ℤ)-2), by change 1 ≤ ((n.1 : ℤ)+1) ∧ (-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2) < -2*((n.1 : ℤ)+1) ∧ ((n.1 : ℤ)+1)+(-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2) ≤ (-((n.1 : ℤ)+1)-(n.2 : ℤ)-2) ∧ 2*(-((n.1 : ℤ)+1)-(n.2 : ℤ)-2) = (-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2)-2; omega⟩
  invFun p := ((p.val.1-1).toNat, (-p.val.2.2-p.val.1-2).toNat)
  left_inv n := by
    rcases n with ⟨a,b⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-2 at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case3bEquiv_val (n : ℕ × ℕ) :
    (i2Case3bEquiv n).val = ((n.1 : ℤ)+1, -2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2, -((n.1 : ℤ)+1)-(n.2 : ℤ)-2) := rfl
def i2Case3cEquiv : (ℕ × ℕ) ≃ I2SpatialRow 5 where
  toFun n := ⟨((n.1 : ℤ)+1, -2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2, -((n.1 : ℤ)+1)-(n.2 : ℤ)-2), by change 1 ≤ ((n.1 : ℤ)+1) ∧ (-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2) < -2*((n.1 : ℤ)+1) ∧ ((n.1 : ℤ)+1)+(-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2) ≤ (-((n.1 : ℤ)+1)-(n.2 : ℤ)-2) ∧ 2*(-((n.1 : ℤ)+1)-(n.2 : ℤ)-2) = (-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2)-2; omega⟩
  invFun p := ((p.val.1-1).toNat, (-p.val.2.2-p.val.1-2).toNat)
  left_inv n := by
    rcases n with ⟨a,b⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-2 at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case3cEquiv_val (n : ℕ × ℕ) :
    (i2Case3cEquiv n).val = ((n.1 : ℤ)+1, -2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2, -((n.1 : ℤ)+1)-(n.2 : ℤ)-2) := rfl
def i2Case3dEquiv : (ℕ × ℕ) ≃ I2SpatialRow 6 where
  toFun n := ⟨((n.1 : ℤ)+1, -2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2, -((n.1 : ℤ)+1)-(n.2 : ℤ)-2), by change 1 ≤ ((n.1 : ℤ)+1) ∧ (-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2) < -2*((n.1 : ℤ)+1) ∧ ((n.1 : ℤ)+1)+(-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2) ≤ (-((n.1 : ℤ)+1)-(n.2 : ℤ)-2) ∧ 2*(-((n.1 : ℤ)+1)-(n.2 : ℤ)-2) = (-2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2)-2; omega⟩
  invFun p := ((p.val.1-1).toNat, (-p.val.2.2-p.val.1-2).toNat)
  left_inv n := by
    rcases n with ⟨a,b⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h = j-2 at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case3dEquiv_val (n : ℕ × ℕ) :
    (i2Case3dEquiv n).val = ((n.1 : ℤ)+1, -2*((n.1 : ℤ)+1)-2*(n.2 : ℤ)-2, -((n.1 : ℤ)+1)-(n.2 : ℤ)-2) := rfl
def i2Case4Equiv : (ℕ × ℕ × ℕ) ≃ I2SpatialRow 7 where
  toFun n := ⟨((n.1 : ℤ)+1, -2*((n.1 : ℤ)+1)-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3, -((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3), by change 1 ≤ ((n.1 : ℤ)+1) ∧ (-2*((n.1 : ℤ)+1)-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) < -2*((n.1 : ℤ)+1) ∧ ((n.1 : ℤ)+1)+(-2*((n.1 : ℤ)+1)-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) ≤ (-((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) ∧ 2*(-((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) ≤ (-2*((n.1 : ℤ)+1)-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)-3; omega⟩
  invFun p := ((p.val.1-1).toNat, (p.val.2.2-p.val.1-p.val.2.1).toNat, (p.val.2.1-2*p.val.2.2-3).toNat)
  left_inv n := by
    rcases n with ⟨a,b,c⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change 1 ≤ k ∧ j < -2*k ∧ k+j ≤ h ∧ 2*h ≤ j-3 at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case4Equiv_val (n : ℕ × ℕ × ℕ) :
    (i2Case4Equiv n).val = ((n.1 : ℤ)+1, -2*((n.1 : ℤ)+1)-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3, -((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) := rfl
def i2Case5Equiv : (ℕ × ℕ × ℕ) ≃ I2SpatialRow 8 where
  toFun n := ⟨((n.1 : ℤ)+1, -2*((n.1 : ℤ)+1)-(n.2.1 : ℤ)-1, -((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-2), by change 1 ≤ ((n.1 : ℤ)+1) ∧ (-2*((n.1 : ℤ)+1)-(n.2.1 : ℤ)-1) < -2*((n.1 : ℤ)+1) ∧ (-((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-2) < ((n.1 : ℤ)+1)+(-2*((n.1 : ℤ)+1)-(n.2.1 : ℤ)-1); omega⟩
  invFun p := ((p.val.1-1).toNat, (-p.val.2.1-2*p.val.1-1).toNat, (p.val.1+p.val.2.1-p.val.2.2-1).toNat)
  left_inv n := by
    rcases n with ⟨a,b,c⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change 1 ≤ k ∧ j < -2*k ∧ h < k+j at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case5Equiv_val (n : ℕ × ℕ × ℕ) :
    (i2Case5Equiv n).val = ((n.1 : ℤ)+1, -2*((n.1 : ℤ)+1)-(n.2.1 : ℤ)-1, -((n.1 : ℤ)+1)-(n.2.1 : ℤ)-(n.2.2 : ℤ)-2) := rfl
def i2Case6aEquiv : (ℕ × ℕ) ≃ I2SpatialRow 9 where
  toFun n := ⟨(0, (n.1 : ℤ), (n.2 : ℤ)-1), by change (0) = 0 ∧ 0 ≤ ((n.1 : ℤ)) ∧ -1 ≤ ((n.2 : ℤ)-1); omega⟩
  invFun p := ((p.val.2.1).toNat, (p.val.2.2+1).toNat)
  left_inv n := by
    rcases n with ⟨a,b⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k = 0 ∧ 0 ≤ j ∧ -1 ≤ h at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case6aEquiv_val (n : ℕ × ℕ) :
    (i2Case6aEquiv n).val = (0, (n.1 : ℤ), (n.2 : ℤ)-1) := rfl
def i2Case6aaEquiv : (ℕ) ≃ I2SpatialRow 10 where
  toFun n := ⟨(0, -1, (n : ℤ)-1), by change (0) = 0 ∧ (-1) = -1 ∧ -1 ≤ ((n : ℤ)-1); omega⟩
  invFun p := (p.val.2.2+1).toNat
  left_inv n := by
    dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k = 0 ∧ j = -1 ∧ -1 ≤ h at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case6aaEquiv_val (n : ℕ) :
    (i2Case6aaEquiv n).val = (0, -1, (n : ℤ)-1) := rfl
def i2Case6aaaEquiv : (ℕ × ℕ) ≃ I2SpatialRow 11 where
  toFun n := ⟨(0, (n.1 : ℤ)-1, -(n.2 : ℤ)-2), by change (0) = 0 ∧ -1 ≤ ((n.1 : ℤ)-1) ∧ (-(n.2 : ℤ)-2) ≤ -2; omega⟩
  invFun p := ((p.val.2.1+1).toNat, (-p.val.2.2-2).toNat)
  left_inv n := by
    rcases n with ⟨a,b⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k = 0 ∧ -1 ≤ j ∧ h ≤ -2 at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case6aaaEquiv_val (n : ℕ × ℕ) :
    (i2Case6aaaEquiv n).val = (0, (n.1 : ℤ)-1, -(n.2 : ℤ)-2) := rfl
def i2Case6bEquiv : (ℕ × ℕ) ≃ I2SpatialRow 12 where
  toFun n := ⟨(-1, (n.1 : ℤ), (n.2 : ℤ)), by change (-1) = -1 ∧ 0 ≤ ((n.1 : ℤ)) ∧ 0 ≤ ((n.2 : ℤ)); omega⟩
  invFun p := ((p.val.2.1).toNat, (p.val.2.2).toNat)
  left_inv n := by
    rcases n with ⟨a,b⟩
    rfl
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k = -1 ∧ 0 ≤ j ∧ 0 ≤ h at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case6bEquiv_val (n : ℕ × ℕ) :
    (i2Case6bEquiv n).val = (-1, (n.1 : ℤ), (n.2 : ℤ)) := rfl
def i2Case6bbEquiv : (ℕ) ≃ I2SpatialRow 13 where
  toFun n := ⟨(-1, -1, (n : ℤ)-1), by change (-1) = -1 ∧ (-1) = -1 ∧ -1 ≤ ((n : ℤ)-1); omega⟩
  invFun p := (p.val.2.2+1).toNat
  left_inv n := by
    dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k = -1 ∧ j = -1 ∧ -1 ≤ h at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case6bbEquiv_val (n : ℕ) :
    (i2Case6bbEquiv n).val = (-1, -1, (n : ℤ)-1) := rfl
def i2Case6bbbEquiv : (ℕ) ≃ I2SpatialRow 14 where
  toFun n := ⟨(-1, -1, -(n : ℤ)-2), by change (-1) = -1 ∧ (-1) = -1 ∧ (-(n : ℤ)-2) ≤ -2; omega⟩
  invFun p := (-p.val.2.2-2).toNat
  left_inv n := by
    dsimp
    omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k = -1 ∧ j = -1 ∧ h ≤ -2 at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case6bbbEquiv_val (n : ℕ) :
    (i2Case6bbbEquiv n).val = (-1, -1, -(n : ℤ)-2) := rfl
def i2Case6cEquiv : (ℕ × ℕ × ℕ) ≃ I2SpatialRow 15 where
  toFun n := ⟨(-(n.1 : ℤ)-2, (n.2.1 : ℤ), (n.2.2 : ℤ)), by change (-(n.1 : ℤ)-2) ≤ -2 ∧ 0 ≤ ((n.2.1 : ℤ)) ∧ 0 ≤ ((n.2.2 : ℤ)); omega⟩
  invFun p := ((-p.val.1-2).toNat, (p.val.2.1).toNat, (p.val.2.2).toNat)
  left_inv n := by
    rcases n with ⟨a,b,c⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k ≤ -2 ∧ 0 ≤ j ∧ 0 ≤ h at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case6cEquiv_val (n : ℕ × ℕ × ℕ) :
    (i2Case6cEquiv n).val = (-(n.1 : ℤ)-2, (n.2.1 : ℤ), (n.2.2 : ℤ)) := rfl
def i2Case6ccEquiv : (ℕ × ℕ) ≃ I2SpatialRow 16 where
  toFun n := ⟨(-(n.1 : ℤ)-2, -1, (n.2 : ℤ)-1), by change (-(n.1 : ℤ)-2) ≤ -2 ∧ (-1) = -1 ∧ -1 ≤ ((n.2 : ℤ)-1); omega⟩
  invFun p := ((-p.val.1-2).toNat, (p.val.2.2+1).toNat)
  left_inv n := by
    rcases n with ⟨a,b⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k ≤ -2 ∧ j = -1 ∧ -1 ≤ h at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case6ccEquiv_val (n : ℕ × ℕ) :
    (i2Case6ccEquiv n).val = (-(n.1 : ℤ)-2, -1, (n.2 : ℤ)-1) := rfl
def i2Case6cccEquiv : (ℕ × ℕ) ≃ I2SpatialRow 17 where
  toFun n := ⟨(-(n.1 : ℤ)-2, -1, -(n.2 : ℤ)-2), by change (-(n.1 : ℤ)-2) ≤ -2 ∧ (-1) = -1 ∧ (-(n.2 : ℤ)-2) ≤ -2; omega⟩
  invFun p := ((-p.val.1-2).toNat, (-p.val.2.2-2).toNat)
  left_inv n := by
    rcases n with ⟨a,b⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k ≤ -2 ∧ j = -1 ∧ h ≤ -2 at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case6cccEquiv_val (n : ℕ × ℕ) :
    (i2Case6cccEquiv n).val = (-(n.1 : ℤ)-2, -1, -(n.2 : ℤ)-2) := rfl
def i2Case7Equiv : (ℕ × ℕ × ℕ) ≃ I2SpatialRow 18 where
  toFun n := ⟨(-(n.1 : ℤ)-1, (n.2.1 : ℤ), -(n.2.2 : ℤ)-1), by change (-(n.1 : ℤ)-1) ≤ -1 ∧ 0 ≤ ((n.2.1 : ℤ)) ∧ (-(n.2.2 : ℤ)-1) ≤ -1; omega⟩
  invFun p := ((-p.val.1-1).toNat, (p.val.2.1).toNat, (-p.val.2.2-1).toNat)
  left_inv n := by
    rcases n with ⟨a,b,c⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k ≤ -1 ∧ 0 ≤ j ∧ h ≤ -1 at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case7Equiv_val (n : ℕ × ℕ × ℕ) :
    (i2Case7Equiv n).val = (-(n.1 : ℤ)-1, (n.2.1 : ℤ), -(n.2.2 : ℤ)-1) := rfl
def i2Case8aEquiv : (Fin 2 × ℕ × ℕ × ℕ) ≃ I2SpatialRow 19 where
  toFun n := ⟨(-(n.2.1 : ℤ), -2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-2, -(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1+(n.2.2.2 : ℤ)), by change (-(n.2.1 : ℤ)) ≤ 0 ∧ (-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-2) < -1 ∧ (-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-2) ≤ (-(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1+(n.2.2.2 : ℤ)) ∧ (-2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-2)-1 ≤ 2*(-(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1+(n.2.2.2 : ℤ)); omega⟩
  invFun p := (⟨((-p.val.2.1-2)%2).toNat, by omega⟩, (-p.val.1).toNat, ((-p.val.2.1-2)/2).toNat, (p.val.2.2+((-p.val.2.1-2)/2)+((-p.val.2.1-2)%2)+1).toNat)
  left_inv n := by
    rcases n with ⟨⟨e,he⟩,a,b,c⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ j-1 ≤ 2*h at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case8aEquiv_val (n : Fin 2 × ℕ × ℕ × ℕ) :
    (i2Case8aEquiv n).val = (-(n.2.1 : ℤ), -2*(n.2.2.1 : ℤ)-(n.1.val : ℤ)-2, -(n.2.2.1 : ℤ)-(n.1.val : ℤ)-1+(n.2.2.2 : ℤ)) := rfl
def i2Case8bEquiv : (ℕ × ℕ) ≃ I2SpatialRow 20 where
  toFun n := ⟨(-(n.1 : ℤ), -2*(n.2 : ℤ)-2, -(n.2 : ℤ)-2), by change (-(n.1 : ℤ)) ≤ 0 ∧ (-2*(n.2 : ℤ)-2) < -1 ∧ (-2*(n.2 : ℤ)-2) ≤ (-(n.2 : ℤ)-2) ∧ 2*(-(n.2 : ℤ)-2) = (-2*(n.2 : ℤ)-2)-2; omega⟩
  invFun p := ((-p.val.1).toNat, (-p.val.2.2-2).toNat)
  left_inv n := by
    rcases n with ⟨a,b⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h = j-2 at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case8bEquiv_val (n : ℕ × ℕ) :
    (i2Case8bEquiv n).val = (-(n.1 : ℤ), -2*(n.2 : ℤ)-2, -(n.2 : ℤ)-2) := rfl
def i2Case8cEquiv : (ℕ × ℕ) ≃ I2SpatialRow 21 where
  toFun n := ⟨(-(n.1 : ℤ), -2*(n.2 : ℤ)-2, -(n.2 : ℤ)-2), by change (-(n.1 : ℤ)) ≤ 0 ∧ (-2*(n.2 : ℤ)-2) < -1 ∧ (-2*(n.2 : ℤ)-2) ≤ (-(n.2 : ℤ)-2) ∧ 2*(-(n.2 : ℤ)-2) = (-2*(n.2 : ℤ)-2)-2; omega⟩
  invFun p := ((-p.val.1).toNat, (-p.val.2.2-2).toNat)
  left_inv n := by
    rcases n with ⟨a,b⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h = j-2 at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case8cEquiv_val (n : ℕ × ℕ) :
    (i2Case8cEquiv n).val = (-(n.1 : ℤ), -2*(n.2 : ℤ)-2, -(n.2 : ℤ)-2) := rfl
def i2Case8dEquiv : (ℕ × ℕ) ≃ I2SpatialRow 22 where
  toFun n := ⟨(-(n.1 : ℤ), -2*(n.2 : ℤ)-2, -(n.2 : ℤ)-2), by change (-(n.1 : ℤ)) ≤ 0 ∧ (-2*(n.2 : ℤ)-2) < -1 ∧ (-2*(n.2 : ℤ)-2) ≤ (-(n.2 : ℤ)-2) ∧ 2*(-(n.2 : ℤ)-2) = (-2*(n.2 : ℤ)-2)-2; omega⟩
  invFun p := ((-p.val.1).toNat, (-p.val.2.2-2).toNat)
  left_inv n := by
    rcases n with ⟨a,b⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h = j-2 at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case8dEquiv_val (n : ℕ × ℕ) :
    (i2Case8dEquiv n).val = (-(n.1 : ℤ), -2*(n.2 : ℤ)-2, -(n.2 : ℤ)-2) := rfl
def i2Case9Equiv : (ℕ × ℕ × ℕ) ≃ I2SpatialRow 23 where
  toFun n := ⟨(-(n.1 : ℤ), -2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3, -(n.2.1 : ℤ)-(n.2.2 : ℤ)-3), by change (-(n.1 : ℤ)) ≤ 0 ∧ (-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) < -1 ∧ (-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) ≤ (-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) ∧ 2*(-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) ≤ (-2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3)-3; omega⟩
  invFun p := ((-p.val.1).toNat, (p.val.2.2-p.val.2.1).toNat, (p.val.2.1-2*p.val.2.2-3).toNat)
  left_inv n := by
    rcases n with ⟨a,b,c⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k ≤ 0 ∧ j < -1 ∧ j ≤ h ∧ 2*h ≤ j-3 at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
@[simp] theorem i2Case9Equiv_val (n : ℕ × ℕ × ℕ) :
    (i2Case9Equiv n).val = (-(n.1 : ℤ), -2*(n.2.1 : ℤ)-(n.2.2 : ℤ)-3, -(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) := rfl
def i2Case10Equiv : (ℕ × ℕ × ℕ) ≃ I2SpatialRow 24 where
  toFun n := ⟨(-(n.1 : ℤ), -(n.2.1 : ℤ)-2, -(n.2.1 : ℤ)-(n.2.2 : ℤ)-3), by change (-(n.1 : ℤ)) ≤ 0 ∧ (-(n.2.1 : ℤ)-2) < -1 ∧ (-(n.2.1 : ℤ)-(n.2.2 : ℤ)-3) < (-(n.2.1 : ℤ)-2); omega⟩
  invFun p := ((-p.val.1).toNat, (-p.val.2.1-2).toNat, (p.val.2.1-p.val.2.2-1).toNat)
  left_inv n := by
    rcases n with ⟨a,b,c⟩
    dsimp
    simp only [Prod.mk.injEq, Fin.mk.injEq, true_and, and_true] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k,j,h⟩, hp⟩
    change k ≤ 0 ∧ j < -1 ∧ h < j at hp
    dsimp
    simp only [Prod.mk.injEq, true_and, and_true] <;> omega
end FourierJacobi.Analysis



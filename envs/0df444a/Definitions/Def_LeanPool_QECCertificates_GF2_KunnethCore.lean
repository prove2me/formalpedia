-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
-- name    : LeanPool_QECCertificates_GF2_KunnethCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:43:36.148911+00:00
-- url     : https://prove2.me/theorems/eaa83a92-b106-48ae-af14-af19248ef98d
-- title:
--   Kunneth Core
-- statement:
--   Definitions and structural lemmas for Kunneth Core, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KunnethCore.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s a b : ℕ}
abbrev VMat (p s : ℕ) := Fin p × Fin s → ZMod 2
def colOf {p s : ℕ} (X : VMat p s) (j : Fin s) : Vec p := fun i => X (i, j)
def rowOf {p s : ℕ} (X : VMat p s) (i : Fin p) : Vec s := fun j => X (i, j)
@[simp] lemma colOf_apply {X : VMat p s} {j : Fin s} {i : Fin p} : colOf X j i = X (i, j) := rfl
@[simp] lemma rowOf_apply {X : VMat p s} {i : Fin p} {j : Fin s} : rowOf X i j = X (i, j) := rfl
@[simp] lemma colOf_add {X Y : VMat p s} {j : Fin s} : colOf (X + Y) j = colOf X j + colOf Y j :=
    rfl
@[simp] lemma colOf_smul {c : ZMod 2} {X : VMat p s} {j : Fin s} :
    colOf (c • X) j = c • colOf X j := rfl
@[simp] lemma rowOf_add {X Y : VMat p s} {i : Fin p} : rowOf (X + Y) i = rowOf X i + rowOf Y i :=
    rfl
@[simp] lemma rowOf_smul {c : ZMod 2} {X : VMat p s} {i : Fin p} :
    rowOf (c • X) i = c • rowOf X i := rfl
def colsSub (U : Submodule (ZMod 2) (Vec p)) : Submodule (ZMod 2) (VMat p s) where
  carrier := {X | ∀ j, colOf X j ∈ U}
  zero_mem' := fun j => U.zero_mem
  add_mem' := fun {X Y} hX hY => fun j => by
    rw [colOf_add]; exact U.add_mem (hX j) (hY j)
  smul_mem' := fun c {X} hX => fun j => by
    rw [colOf_smul]; exact U.smul_mem c (hX j)
def rowsSub (W : Submodule (ZMod 2) (Vec s)) : Submodule (ZMod 2) (VMat p s) where
  carrier := {X | ∀ i, rowOf X i ∈ W}
  zero_mem' := fun i => W.zero_mem
  add_mem' := fun {X Y} hX hY => fun i => by
    rw [rowOf_add]; exact W.add_mem (hX i) (hY i)
  smul_mem' := fun c {X} hX => fun i => by
    rw [rowOf_smul]; exact W.smul_mem c (hX i)
@[simp] lemma mem_colsSub {U : Submodule (ZMod 2) (Vec p)} {X : VMat p s} :
    X ∈ colsSub U ↔ ∀ j, colOf X j ∈ U :=
  ⟨fun h => h, fun h => h⟩
@[simp] lemma mem_rowsSub {W : Submodule (ZMod 2) (Vec s)} {X : VMat p s} :
    X ∈ rowsSub W ↔ ∀ i, rowOf X i ∈ W :=
  ⟨fun h => h, fun h => h⟩
noncomputable def colsSubEquiv (U : Submodule (ZMod 2) (Vec p)) :
    ↥(colsSub (s := s) U) ≃ₗ[ZMod 2] (Fin s → U) where
  toFun X := fun j => ⟨colOf X.1 j, X.2 j⟩
  invFun f := ⟨fun ij => (f ij.2).1 ij.1, fun j => (f j).2⟩
  left_inv X := by ext ⟨i, j⟩; rfl
  right_inv f := by ext j i; rfl
  map_add' X Y := by ext j i; rfl
  map_smul' c X := by ext j i; rfl
noncomputable def rowsSubEquiv (W : Submodule (ZMod 2) (Vec s)) :
    ↥(rowsSub (p := p) (s := s) W) ≃ₗ[ZMod 2] (Fin p → W) where
  toFun X := fun i => ⟨rowOf X.1 i, X.2 i⟩
  invFun f := ⟨fun ij => (f ij.1).1 ij.2, fun i => (f i).2⟩
  left_inv X := by ext ⟨i, j⟩; rfl
  right_inv f := by ext i j; rfl
  map_add' X Y := by ext i j; rfl
  map_smul' c X := by ext i j; rfl
noncomputable def vee (u : Fin a → Vec p) : VMat a s →ₗ[ZMod 2] VMat p s where
  toFun C := fun ij => ∑ k, C (k, ij.2) * u k ij.1
  map_add' C D := by
    ext ⟨i, j⟩
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c C := by
    ext ⟨i, j⟩
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]
noncomputable def wedge (L : Vec p →ₗ[ZMod 2] (Fin a → ZMod 2)) : VMat p s →ₗ[ZMod 2] VMat a s where
  toFun X := fun kj => L (colOf X kj.2) kj.1
  map_add' X Y := by
    ext ⟨k, j⟩
    simp only [Pi.add_apply, colOf_add, map_add, Pi.add_apply]
  map_smul' c X := by
    ext ⟨k, j⟩
    simp only [Pi.smul_apply, colOf_smul, map_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
end QECCertificates



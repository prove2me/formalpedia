-- Prove2me | Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
-- name    : Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:13.624997+00:00
-- url     : https://prove2.me/theorems/865f0f7d-466d-4513-ad12-3b46e3c3df4e
-- title:
--   Mem Coboundaries Of Is One Coboundary
-- statement:
--   Definitions and structural lemmas for Mem Coboundaries Of Is One Coboundary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/MemCoboundariesOfIsOneCoboundary.lean

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CoboundaryTransfers
namespace WachMod
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  (W : WachMod B M D)
theorem smulO_eq (c : O) (x : D) : c • x = algebraMap O A c • x := by
  rw [algebraMap_smul]
theorem smulO_mem (c : O) {x : D} (hx : x ∈ W.N) : c • x ∈ W.N := by
  rw [smulO_eq (A := A)]; exact W.N.smul_mem _ hx
theorem qInv_zero : W.QInv 0 := by
  simp only [QInv, smul_zero]; exact W.N.zero_mem
theorem qInv_add {y y' : D} (hy : W.QInv y) (hy' : W.QInv y') : W.QInv (y + y') := by
  simp only [QInv, smul_add]; exact W.N.add_mem hy hy'
theorem qInv_smul (a : A) {y : D} (hy : W.QInv y) : W.QInv (a • y) := by
  simp only [QInv]; rw [smul_comm]; exact W.N.smul_mem a hy
theorem qInv_smulO (c : O) {y : D} (hy : W.QInv y) : W.QInv (c • y) := by
  rw [smulO_eq (A := A)]; exact W.qInv_smul _ hy
theorem xN_zero : W.XN 0 := ⟨0, W.N.zero_mem, (smul_zero _).symm⟩
theorem xN_add {z z' : D} (hz : W.XN z) (hz' : W.XN z') : W.XN (z + z') := by
  obtain ⟨n, hn, rfl⟩ := hz; obtain ⟨n', hn', rfl⟩ := hz'
  exact ⟨n + n', W.N.add_mem hn hn', (smul_add _ _ _).symm⟩
theorem xN_smul (a : A) {z : D} (hz : W.XN z) : W.XN (a • z) := by
  obtain ⟨n, hn, rfl⟩ := hz
  exact ⟨a • n, W.N.smul_mem a hn, smul_comm _ _ _⟩
theorem xN_smulO (c : O) {z : D} (hz : W.XN z) : W.XN (c • z) := by
  rw [smulO_eq (A := A)]; exact W.xN_smul _ hz
theorem cont_pow_X_pow_eq_zero_of_lt : W.C1 0 0 := ⟨W.qInv_zero, W.xN_zero⟩
theorem isOneCochain_add {y z y' z' : D} (h : W.C1 y z) (h' : W.C1 y' z') : W.C1 (y + y') (z + z') :=
  ⟨W.qInv_add h.1 h'.1, W.xN_add h.2 h'.2⟩
theorem isOneCochain_smul_of_tower (c : O) {y z : D} (h : W.C1 y z) : W.C1 (c • y) (c • z) :=
  ⟨W.qInv_smulO c h.1, W.xN_smulO c h.2⟩
theorem cont_X_pow_pow_eq_zero_of_gt : W.C2 0 := ⟨0, W.qInv_zero, (smul_zero _).symm⟩
theorem isTwoCochain_add {ω ω' : D} (h : W.C2 ω) (h' : W.C2 ω') : W.C2 (ω + ω') := by
  obtain ⟨y, hy, rfl⟩ := h; obtain ⟨y', hy', rfl⟩ := h'
  exact ⟨y + y', W.qInv_add hy hy', (smul_add _ _ _).symm⟩
theorem isTwoCochain_smul (a : A) {ω : D} (h : W.C2 ω) : W.C2 (a • ω) := by
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨a • y, W.qInv_smul a hy, smul_comm _ _ _⟩
theorem diffOne_zero : W.d1 0 0 = 0 := by simp [d1]
theorem diffOne_add (y z y' z' : D) : W.d1 (y + y') (z + z') = W.d1 y z + W.d1 y' z' := by
  simp only [d1, map_add]; abel
theorem diffOne_smul_of_tower (c : O) (y z : D) : W.d1 (c • y) (c • z) = c • W.d1 y z := by
  simp only [d1, map_smul, smul_sub]
theorem cocycle_zero : W.Cocycle 0 0 := ⟨W.cont_pow_X_pow_eq_zero_of_lt, W.diffOne_zero⟩
theorem cocycle_add {y z y' z' : D} (h : W.Cocycle y z) (h' : W.Cocycle y' z') :
    W.Cocycle (y + y') (z + z') :=
  ⟨W.isOneCochain_add h.1 h'.1, by rw [W.diffOne_add, h.2, h'.2, add_zero]⟩
theorem cocycle_smulO (c : O) {y z : D} (h : W.Cocycle y z) : W.Cocycle (c • y) (c • z) :=
  ⟨W.isOneCochain_smul_of_tower c h.1, by rw [W.diffOne_smul_of_tower, h.2, smul_zero]⟩
theorem isCob1_zero : W.IsCob1 0 0 := ⟨0, W.N.zero_mem, by simp, by simp⟩
theorem isCob1_add {y z y' z' : D} (h : W.IsCob1 y z) (h' : W.IsCob1 y' z') :
    W.IsCob1 (y + y') (z + z') := by
  obtain ⟨x, hx, rfl, rfl⟩ := h; obtain ⟨x', hx', rfl, rfl⟩ := h'
  refine ⟨x + x', W.N.add_mem hx hx', ?_, ?_⟩ <;> simp only [map_add] <;> abel
theorem isCob1_smulO (c : O) {y z : D} (h : W.IsCob1 y z) : W.IsCob1 (c • y) (c • z) := by
  obtain ⟨x, hx, rfl, rfl⟩ := h
  exact ⟨c • x, W.smulO_mem c hx, by rw [map_smul, smul_sub], by rw [map_smul, smul_sub]⟩
theorem isCob2_zero : W.IsCob2 0 := ⟨0, 0, W.cont_pow_X_pow_eq_zero_of_lt, W.diffOne_zero.symm⟩
theorem isCob2_add {ω ω' : D} (h : W.IsCob2 ω) (h' : W.IsCob2 ω') : W.IsCob2 (ω + ω') := by
  obtain ⟨y, z, hc, rfl⟩ := h; obtain ⟨y', z', hc', rfl⟩ := h'
  exact ⟨y + y', z + z', W.isOneCochain_add hc hc', (W.diffOne_add _ _ _ _).symm⟩
theorem isCob2_smulO (c : O) {ω : D} (h : W.IsCob2 ω) : W.IsCob2 (c • ω) := by
  obtain ⟨y, z, hc, rfl⟩ := h
  exact ⟨c • y, c • z, W.isOneCochain_smul_of_tower c hc, (W.diffOne_smul_of_tower _ _ _).symm⟩
def qInvSub : Submodule A D where
  carrier := {y | W.QInv y}
  add_mem' := W.qInv_add
  zero_mem' := W.qInv_zero
  smul_mem' := fun a _ hy => W.qInv_smul a hy
def xNSub : Submodule A D where
  carrier := {z | W.XN z}
  add_mem' := W.xN_add
  zero_mem' := W.xN_zero
  smul_mem' := fun a _ hz => W.xN_smul a hz
def twoCochains : Submodule A D where
  carrier := {ω | W.C2 ω}
  add_mem' := W.isTwoCochain_add
  zero_mem' := W.cont_X_pow_pow_eq_zero_of_gt
  smul_mem' := fun a _ h => W.isTwoCochain_smul a h
def cocycleSub : Submodule O (D × D) where
  carrier := {pr | W.Cocycle pr.1 pr.2}
  add_mem' := fun h h' => W.cocycle_add h h'
  zero_mem' := W.cocycle_zero
  smul_mem' := fun c _ h => W.cocycle_smulO c h
def isCob1Sub : Submodule O (D × D) where
  carrier := {pr | W.IsCob1 pr.1 pr.2}
  add_mem' := fun h h' => W.isCob1_add h h'
  zero_mem' := W.isCob1_zero
  smul_mem' := fun c _ h => W.isCob1_smulO c h
def isCob2Sub : Submodule O D where
  carrier := {ω | W.IsCob2 ω}
  add_mem' := W.isCob2_add
  zero_mem' := W.isCob2_zero
  smul_mem' := fun c _ h => W.isCob2_smulO c h
end WachMod
end Formalism.CoboundaryTransfers



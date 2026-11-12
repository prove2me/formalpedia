-- Prove2me | Definitions.Def_OddOrder_GroupTheory_FixedSubgroup
-- name    : OddOrder_GroupTheory_FixedSubgroup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:21.904197+00:00
-- url     : https://prove2.me/theorems/f09ffd92-d91a-4887-87ea-2834ca6a351f
-- title:
--   Fixed subgroup of an automorphic action
-- statement:
--   Defines the fixed-point subgroup $C_H(K)$ of an action $\varphi:L\to\mathrm{Aut}(H)$ by a subgroup $K\le L$. It was split out of the coprime-action file so that the forward-dependency file for Isaacs Ch. 3 §3E can refer to it without an import cycle through Chapter 6.
--
--   Main definitions: `fixedSubgroup` (the points of $H$ fixed by every element of $K$) and a private helper `fixerSubgroup` (the elements of $L$ fixing a given point of $H$).
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/FixedSubgroup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/FixedSubgroup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.GroupAction.Basic

namespace OddOrder.GroupTheory

variable {L H : Type*} [Group L] [Group H]

/-- The subgroup `C_H(K)` of points of `H` fixed by every element of a subgroup `K ≤ L`,
under an action `φ : L →* MulAut H`.  This is a subgroup of `H` because each `φ l` is a
group automorphism. -/
def fixedSubgroup (φ : L →* MulAut H) (K : Subgroup L) : Subgroup H where
  carrier := {h | ∀ l ∈ K, φ l h = h}
  one_mem' l _ := map_one (φ l)
  mul_mem' ha hb l hl := by rw [map_mul, ha l hl, hb l hl]
  inv_mem' ha l hl := by rw [map_inv, ha l hl]

@[simp] theorem mem_fixedSubgroup {φ : L →* MulAut H} {K : Subgroup L} {x : H} :
    x ∈ fixedSubgroup φ K ↔ ∀ l ∈ K, φ l x = x := Iff.rfl

/-- Fixing the elements of a *larger* subgroup yields a *smaller* fixed subgroup. -/
theorem fixedSubgroup_antitone (φ : L →* MulAut H) {K K' : Subgroup L} (h : K ≤ K') :
    fixedSubgroup φ K' ≤ fixedSubgroup φ K :=
  fun _ hx l hl => hx l (h hl)

/-- Private helper: the elements of `L` fixing a given point `x ∈ H` form a subgroup
(the `φ`-stabilizer of `x`).  Kept private: publicly this is `MulAction.stabilizer` for
the action induced by `φ`, so a public duplicate would be wrapper debt. -/
private def fixerSubgroup (φ : L →* MulAut H) (x : H) : Subgroup L where
  carrier := {l | φ l x = x}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, MulAut.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_inv, MulAut.inv_def]
    exact (MulEquiv.symm_apply_eq (φ a)).mpr ha.symm

private theorem mem_fixedSubgroup_iff_le_fixerSubgroup {φ : L →* MulAut H} {K : Subgroup L}
    {x : H} : x ∈ fixedSubgroup φ K ↔ K ≤ fixerSubgroup φ x := Iff.rfl

@[simp] theorem fixedSubgroup_bot (φ : L →* MulAut H) : fixedSubgroup φ ⊥ = ⊤ :=
  top_le_iff.mp fun _ _ => mem_fixedSubgroup_iff_le_fixerSubgroup.mpr bot_le

end OddOrder.GroupTheory



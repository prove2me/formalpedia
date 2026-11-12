-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_AInvariantSubrep
-- name    : OddOrder_GroupTheory_RepresentationTheory_AInvariantSubrep
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:39:16.493253+00:00
-- url     : https://prove2.me/theorems/7fbda376-c752-4333-98c3-a622bf8b5de0
-- title:
--   $\varphi$-invariant subgroups as subrepresentations of `elabRepresentation`
-- statement:
--   Provides the bridge for the imprimitive (non-Galois) branch of Peterfalvi (9.7)(a): the $U$-invariant order-$p$ Clifford blocks of the chief factor become subrepresentations.
--
--   Main declarations: `elabSubmoduleSubgroupEquiv` (The subgroup ↔ ZMod p-submodule order-isomorphism Submodule (ZMod p) (Additive K) ≃o…); `aInvariantSubrep` (A `φ`-invariant subgroup as a subrepresentation).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/AInvariantSubrep.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/AInvariantSubrep.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_WielandtElabBridge
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LineScalarCharacter
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Algebra.Module.ZMod

namespace OddOrder.GroupTheory

open OddOrder.Isaacs.Ch03

variable {A K : Type*} [Group A] [CommGroup K] {p : ℕ} [Module (ZMod p) (Additive K)]
  {φ : A →* MulAut K}

/-- The subgroup ↔ `ZMod p`-submodule order-isomorphism `Submodule (ZMod p) (Additive K) ≃o
Subgroup K` (the composite of `AddSubgroup.toZModSubmodule` and `AddSubgroup.toSubgroup'`, exactly
the correspondence used inside `elabRepresentation_isIrreducible`). -/
def elabSubmoduleSubgroupEquiv (p : ℕ) [Module (ZMod p) (Additive K)] :
    Submodule (ZMod p) (Additive K) ≃o Subgroup K :=
  (AddSubgroup.toZModSubmodule p).symm.trans AddSubgroup.toSubgroup'

theorem mem_elabSubmoduleSubgroupEquiv (W : Submodule (ZMod p) (Additive K)) (x : K) :
    x ∈ elabSubmoduleSubgroupEquiv p W ↔ Additive.ofMul x ∈ W := by
  simp only [elabSubmoduleSubgroupEquiv, OrderIso.trans_apply, AddSubgroup.mem_toSubgroup',
    AddSubgroup.toZModSubmodule_symm, Submodule.mem_toAddSubgroup]

/-- Membership in the submodule attached to a subgroup `J`: `v ∈ Φ⁻¹ J ↔ Additive.toMul v ∈ J`. -/
theorem mem_symm_elabSubmoduleSubgroupEquiv (J : Subgroup K) (v : Additive K) :
    v ∈ (elabSubmoduleSubgroupEquiv p).symm J ↔ Additive.toMul v ∈ J := by
  have h := mem_elabSubmoduleSubgroupEquiv (p := p) ((elabSubmoduleSubgroupEquiv p).symm J)
    (Additive.toMul v)
  rw [OrderIso.apply_symm_apply] at h
  exact h.symm

/-- **A `φ`-invariant subgroup as a subrepresentation.**  A subgroup `J` of the elementary abelian
`p`-group `K` invariant under the action `φ : A →* MulAut K` gives a subrepresentation of
`elabRepresentation p φ`, carried on the submodule `Additive.ofMul '' J`.  The `apply_mem`
obligation is the invariance `φ a g ∈ J` (`IsAInvariant.smul_mem`) transported through the action
bridge `elabRepresentation_apply`. -/
def aInvariantSubrep {J : Subgroup K} (hJ : IsAInvariant φ J) :
    Subrepresentation (elabRepresentation p φ) where
  toSubmodule := (elabSubmoduleSubgroupEquiv p).symm J
  apply_mem_toSubmodule g v hv := by
    rw [mem_symm_elabSubmoduleSubgroupEquiv] at hv ⊢
    -- `toMul (elabRepresentation p φ g v) = φ g (toMul v)` by `rfl` (`elabRepresentation_apply`).
    exact hJ.smul_mem g hv

@[simp] theorem aInvariantSubrep_toSubmodule {J : Subgroup K} (hJ : IsAInvariant φ J) :
    (aInvariantSubrep hJ).toSubmodule = (elabSubmoduleSubgroupEquiv p).symm J := rfl

end OddOrder.GroupTheory



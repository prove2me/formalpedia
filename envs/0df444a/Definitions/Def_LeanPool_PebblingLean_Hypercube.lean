-- Prove2me | Definitions.Def_LeanPool_PebblingLean_Hypercube
-- name    : LeanPool_PebblingLean_Hypercube
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:49:35.836537+00:00
-- url     : https://prove2.me/theorems/006fe000-c3b2-4a85-a2fa-ead5e64fbb04
-- title:
--   Hypercube
-- statement:
--   Definitions and structural lemmas for Hypercube, from Lior Pachter; LeanPool contributors's pinned Optimal Pebbling Number of the Hypercube development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Hypercube.lean

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Bound.Init
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace PebblingLean
abbrev HypercubeVertex (n : ℕ) := Fin n → Bool
namespace Hypercube
def dist {n : ℕ} (x y : HypercubeVertex n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card
def diffSet {n : ℕ} (x y : HypercubeVertex n) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => x i ≠ y i)
def fromDiffSet {n : ℕ} (base : HypercubeVertex n) (s : Finset (Fin n)) :
    HypercubeVertex n :=
  fun i => if i ∈ s then Bool.not (base i) else base i
@[simp]
theorem diffSet_fromDiffSet {n : ℕ} (base : HypercubeVertex n) (s : Finset (Fin n)) :
    diffSet base (fromDiffSet base s) = s := by
  ext i
  by_cases hi : i ∈ s <;> simp [diffSet, fromDiffSet, hi]
@[simp]
theorem fromDiffSet_diffSet {n : ℕ} (base v : HypercubeVertex n) :
    fromDiffSet base (diffSet base v) = v := by
  funext i
  by_cases hsame : base i = v i
  · have hnot : i ∉ diffSet base v := by
      simp [diffSet, hsame]
    simp [fromDiffSet, hnot, hsame]
  · have hin : i ∈ diffSet base v := by
      simp [diffSet, hsame]
    have hflip : Bool.not (base i) = v i := by
      exact (Bool.eq_not_iff.mpr (Ne.symm hsame)).symm
    simp [fromDiffSet, hin, hflip]
def diffSetEquiv {n : ℕ} (base : HypercubeVertex n) :
    HypercubeVertex n ≃ Finset (Fin n) where
  toFun := diffSet base
  invFun := fromDiffSet base
  left_inv := fromDiffSet_diffSet base
  right_inv := diffSet_fromDiffSet base
@[simp]
theorem dist_self {n : ℕ} (x : HypercubeVertex n) : dist x x = 0 := by
  simp [dist]
theorem dist_comm {n : ℕ} (x y : HypercubeVertex n) : dist x y = dist y x := by
  simp [dist, ne_comm]
def graph (n : ℕ) : Graph (HypercubeVertex n) where
  Adj x y := dist x y = 1
  symm := by
    intro x y h
    rw [dist_comm x y] at h
    exact h
  loopless := by
    simp_all
end Hypercube
end PebblingLean



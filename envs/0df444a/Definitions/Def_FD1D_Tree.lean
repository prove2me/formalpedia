-- Prove2me | Definitions.Def_FD1D_Tree
-- name    : FD1D_Tree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:48:13.820573+00:00
-- url     : https://prove2.me/theorems/828c60c7-79d7-4703-b8cb-3351f60bb148
-- title:
--   Tree
-- statement:
--   Definitions and structural lemmas for Tree, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean

import Definitions.Def_FD1D_Basic
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


set_option autoImplicit true
namespace FD1D
noncomputable section
abbrev DyadicNode (d : ℕ) := Fin (2 ^ d)
def dyadicRoot : DyadicNode 0 := 0
def childrenEquiv (d : ℕ) : DyadicNode d × Fin 2 ≃ DyadicNode (d + 1) :=
  finProdFinEquiv.trans (finCongr (by simp [pow_succ]))
def leftChild {d : ℕ} (v : DyadicNode d) : DyadicNode (d + 1) :=
  childrenEquiv d (v, 0)
def rightChild {d : ℕ} (v : DyadicNode d) : DyadicNode (d + 1) :=
  childrenEquiv d (v, 1)
@[simp] theorem leftChild_val {d : ℕ} (v : DyadicNode d) :
    (leftChild v).val = 2 * v.val := by
  simp [leftChild, childrenEquiv, finProdFinEquiv]
@[simp] theorem rightChild_val {d : ℕ} (v : DyadicNode d) :
    (rightChild v).val = 2 * v.val + 1 := by
  simp [rightChild, childrenEquiv, finProdFinEquiv]
  omega
def parent {d : ℕ} (v : DyadicNode (d + 1)) : DyadicNode d :=
  (childrenEquiv d).symm v |>.1
@[simp] theorem parent_leftChild {d : ℕ} (v : DyadicNode d) :
    parent (leftChild v) = v := by
  simp [parent, leftChild]
@[simp] theorem parent_rightChild {d : ℕ} (v : DyadicNode d) :
    parent (rightChild v) = v := by
  simp [parent, rightChild]
theorem leftChild_ne_rightChild {d : ℕ} (v : DyadicNode d) :
    leftChild v ≠ rightChild v := by
  intro h
  have hs := congrArg (fun x => x.2.val) ((childrenEquiv d).injective h)
  norm_num at hs
def descendantsEquiv {d L : ℕ} (hdL : d ≤ L) :
    DyadicNode d × Fin (2 ^ (L - d)) ≃ DyadicNode L :=
  finProdFinEquiv.trans (finCongr (by
    calc
      2 ^ d * 2 ^ (L - d) = 2 ^ (d + (L - d)) := by
        rw [pow_add]
      _ = 2 ^ L := by rw [Nat.add_sub_of_le hdL]))
def descendantLeaf {d L : ℕ} (hdL : d ≤ L) (v : DyadicNode d)
    (j : Fin (2 ^ (L - d))) : DyadicNode L :=
  descendantsEquiv hdL (v, j)
theorem descendantLeaf_val {d L : ℕ} (hdL : d ≤ L) (v : DyadicNode d)
    (j : Fin (2 ^ (L - d))) :
    (descendantLeaf hdL v j).val = v.val * 2 ^ (L - d) + j.val := by
  simp [descendantLeaf, descendantsEquiv, finProdFinEquiv]
  ac_rfl
def descendantEmbedding {d L : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    Fin (2 ^ (L - d)) ↪ DyadicNode L where
  toFun := descendantLeaf hdL v
  inj' := by
    intro i j hij
    have hp := (descendantsEquiv hdL).injective hij
    exact congrArg Prod.snd hp
def leafBlock {d L : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    Finset (DyadicNode L) :=
  Finset.univ.map (descendantEmbedding hdL v)
@[simp] theorem card_leafBlock {d L : ℕ} (hdL : d ≤ L)
    (v : DyadicNode d) :
    (leafBlock hdL v).card = 2 ^ (L - d) := by
  simp [leafBlock]
theorem mem_leafBlock_iff {d L : ℕ} (hdL : d ≤ L)
    (v : DyadicNode d) (w : DyadicNode L) :
    w ∈ leafBlock hdL v ↔
      ∃ j : Fin (2 ^ (L - d)), descendantLeaf hdL v j = w := by
  rw [leafBlock, Finset.mem_map]
  simp only [Finset.mem_univ, true_and]
  change (∃ j, descendantLeaf hdL v j = w) ↔ _
  rfl
theorem mem_leafBlock_interval {d L : ℕ} (hdL : d ≤ L)
    (v : DyadicNode d) (w : DyadicNode L) :
    w ∈ leafBlock hdL v ↔
      v.val * 2 ^ (L - d) ≤ w.val ∧
        w.val < (v.val + 1) * 2 ^ (L - d) := by
  rw [mem_leafBlock_iff]
  constructor
  · rintro ⟨j, rfl⟩
    rw [descendantLeaf_val]
    constructor
    · omega
    · have := j.isLt
      simp [Nat.add_mul]
  · intro hw
    simp [Nat.add_mul] at hw
    have hk : 0 < 2 ^ (L - d) := Nat.two_pow_pos _
    let j : Fin (2 ^ (L - d)) :=
      ⟨w.val - v.val * 2 ^ (L - d), by omega⟩
    refine ⟨j, Fin.ext ?_⟩
    rw [descendantLeaf_val]
    dsimp [j]
    omega
theorem leafBlock_disjoint {d L : ℕ} (hdL : d ≤ L)
    {v w : DyadicNode d} (hvw : v ≠ w) :
    Disjoint (leafBlock hdL v) (leafBlock hdL w) := by
  rw [Finset.disjoint_left]
  intro z hzv hzw
  rw [mem_leafBlock_iff] at hzv hzw
  obtain ⟨i, hi⟩ := hzv
  obtain ⟨j, hj⟩ := hzw
  have hp : (v, i) = (w, j) := by
    apply (descendantsEquiv hdL).injective
    exact hi.trans hj.symm
  exact hvw (congrArg Prod.fst hp)
theorem leafBlock_children {d L : ℕ} (hdL : d < L)
    (v : DyadicNode d) :
    leafBlock (Nat.le_of_lt hdL) v =
      leafBlock (show d + 1 ≤ L by omega) (leftChild v) ∪
        leafBlock (show d + 1 ≤ L by omega) (rightChild v) := by
  ext w
  rw [Finset.mem_union]
  rw [mem_leafBlock_interval, mem_leafBlock_interval, mem_leafBlock_interval]
  have hsub : L - d = (L - (d + 1)) + 1 := by omega
  rw [hsub, pow_succ]
  simp [Nat.add_mul]
  ring_nf
  omega
def nodeMass (d : ℕ) (_ : DyadicNode d) : ℝ :=
  ((2 : ℝ) ^ d)⁻¹
@[simp] theorem nodeMass_root :
    nodeMass 0 dyadicRoot = 1 := by
  simp [nodeMass]
theorem nodeMass_child {d : ℕ} (v : DyadicNode d) (side : Fin 2) :
    nodeMass (d + 1) (childrenEquiv d (v, side)) = nodeMass d v / 2 := by
  simp [nodeMass, pow_succ]
  ring
@[simp] theorem nodeMass_leftChild {d : ℕ} (v : DyadicNode d) :
    nodeMass (d + 1) (leftChild v) = nodeMass d v / 2 :=
  nodeMass_child v 0
@[simp] theorem nodeMass_rightChild {d : ℕ} (v : DyadicNode d) :
    nodeMass (d + 1) (rightChild v) = nodeMass d v / 2 :=
  nodeMass_child v 1
structure LeafInventory (L m : ℕ) where
  count : DyadicNode L → ℕ
  total_count : ∑ v, count v = m
structure AggregatedInventory (L m : ℕ) where
  leaf : LeafInventory L m
  count : ∀ d, DyadicNode d → ℕ
  count_leaf : count L = leaf.count
  count_children : ∀ d, d < L → ∀ v,
    count d v = count (d + 1) (leftChild v) +
      count (d + 1) (rightChild v)
  count_root : count 0 dyadicRoot = m
namespace LeafInventory
def nodeCount {L m d : ℕ} (I : LeafInventory L m) (hdL : d ≤ L)
    (v : DyadicNode d) : ℕ :=
  ∑ w ∈ leafBlock hdL v, I.count w
@[simp] theorem nodeCount_leaf {L m : ℕ} (I : LeafInventory L m)
    (v : DyadicNode L) :
    I.nodeCount le_rfl v = I.count v := by
  have hblock : leafBlock (le_refl L) v = {v} := by
    ext w
    rw [mem_leafBlock_interval, Finset.mem_singleton]
    simp only [Nat.sub_self, pow_zero, mul_one]
    constructor
    · intro hw
      apply Fin.ext
      omega
    · rintro rfl
      omega
  simp [nodeCount, hblock]
@[simp] theorem nodeCount_root {L m : ℕ} (I : LeafInventory L m) :
    I.nodeCount (Nat.zero_le L) dyadicRoot = m := by
  have hblock : leafBlock (Nat.zero_le L) dyadicRoot = Finset.univ := by
    ext w
    rw [mem_leafBlock_interval]
    simp [dyadicRoot, w.isLt]
  simpa [nodeCount, hblock] using I.total_count
theorem nodeCount_children {L m d : ℕ} (I : LeafInventory L m)
    (hdL : d < L) (v : DyadicNode d) :
    I.nodeCount (Nat.le_of_lt hdL) v =
      I.nodeCount (Nat.succ_le_iff.mpr hdL) (leftChild v) +
        I.nodeCount (Nat.succ_le_iff.mpr hdL) (rightChild v) := by
  rw [nodeCount, leafBlock_children hdL v]
  exact Finset.sum_union
    (leafBlock_disjoint (show d + 1 ≤ L by omega)
      (leftChild_ne_rightChild v))
def aggregate {L m : ℕ} (I : LeafInventory L m) :
    AggregatedInventory L m where
  leaf := I
  count d v := if hdL : d ≤ L then I.nodeCount hdL v else 0
  count_leaf := by
    funext v
    simp
  count_children d hdL v := by
    simp only [dif_pos (Nat.le_of_lt hdL),
      dif_pos (Nat.succ_le_iff.mpr hdL)]
    exact I.nodeCount_children hdL v
  count_root := by
    simp
end LeafInventory
structure CoherentTreeLabel (L : ℕ) (A : Type*) [AddCommMonoid A] where
  value : ∀ d, DyadicNode d → A
  children : ∀ d, d < L → ∀ v,
    value d v = value (d + 1) (leftChild v) +
      value (d + 1) (rightChild v)
def levelSum {A : Type*} [AddCommMonoid A]
    (f : ∀ d, DyadicNode d → A) (d : ℕ) : A :=
  ∑ v, f d v
def weightedLevel (f : ∀ d, DyadicNode d → ℝ) (d : ℕ) : ℝ :=
  ∑ v, nodeMass d v * f d v
def childAverage (f : ∀ d, DyadicNode d → ℝ) (d : ℕ)
    (v : DyadicNode d) : ℝ :=
  (f (d + 1) (leftChild v) + f (d + 1) (rightChild v)) / 2
def nonrootWeightedSum (f : ∀ d, DyadicNode d → ℝ) (L : ℕ) : ℝ :=
  ∑ d ∈ Finset.range L, weightedLevel f (d + 1)
def internalWeightedSum (f : ∀ d, DyadicNode d → ℝ) (L : ℕ) : ℝ :=
  ∑ d ∈ Finset.range L, weightedLevel f d
def hazardEnergy (h : ∀ d, DyadicNode d → ℝ) (d : ℕ) : ℝ :=
  weightedLevel (fun d v => (h d v) ^ 2) d
def bellmanDrift
    (L : ℕ) (a : ℝ)
    (N q : ∀ d, DyadicNode d → ℝ) : ℝ :=
  ∑ d ∈ Finset.range L,
    ∑ v : DyadicNode (d + 1),
      (nodeMass (d + 1) v) ^ 2 *
        (nodeMass (d + 1) v - q (d + 1) v) /
          (N (d + 1) v + a)
def nonrootMassSqSum (L : ℕ) : ℝ :=
  ∑ d ∈ Finset.range L,
    ∑ v : DyadicNode (d + 1), (nodeMass (d + 1) v) ^ 2
end
end FD1D



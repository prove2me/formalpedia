-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Block
-- name    : Complexitylib_0ebd467_Foundations_Data_BitString_Block
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:13.509616+00:00
-- url     : https://prove2.me/theorems/b5e2f698-9e8b-44ef-86e2-c32daef02b13
-- title:
--   Complexity.Foundations.Data.BitString.Block — Blocks of bit strings and finite tuples
-- statement:
--   This is module `Complexity.Foundations.Data.BitString.Block` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A tuple of `m * k` entries (in particular, a `BitString (m * k)`) is read as `m` consecutive
--   blocks of `k` entries through `finProdFinEquiv`: entry `j` of block `i` is entry
--   `finProdFinEquiv (i, j)` of the tuple (`BitString.block`). Cutting a tuple into its blocks is an
--   equivalence `(Fin (m * k) → α) ≃ (Fin m → Fin k → α)` (`BitString.blocksEquiv`). The positions of
--   the blocks (`BitString.blockBits`) are pairwise disjoint, and gluing two tuples along the
--   positions of one block takes that block from the first tuple and every other block from the second
--   (`BitString.block_piecewise`).
--
--   ### Main definitions
--
--   * `Cslib.BitString.block`: the `i`-th block of `k` entries of a tuple of `m * k` entries.
--   * `Cslib.BitString.blocksEquiv`: cutting a tuple into its blocks; its inverse reads entry `p` of
--     the tuple in its block (`BitString.blocksEquiv_symm_apply`).
--   * `Cslib.BitString.blockBits`: the positions of the entries of a block.
--   * `Cslib.BitString.listBlock`: a block of a list (`BitString.listBlock_ofFn`).
--
--   ### Main results
--
--   * `Cslib.BitString.pairwiseDisjoint_blockBits`: blocks occupy disjoint positions.
--   * `Cslib.BitString.block_piecewise`: gluing two tuples along one block.
--
--   **Contents.** The module is published as a whole: 11 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_BitString_Block`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/BitString/Block.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Cslib_254e30e_Foundations_Data_BitString
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/- Prove2me definition bundle for `Complexity.Foundations.Data.BitString.Block` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Blocks of bit strings and finite tuples

A tuple of `m * k` entries (in particular, a `BitString (m * k)`) is read as `m` consecutive
blocks of `k` entries through `finProdFinEquiv`: entry `j` of block `i` is entry
`finProdFinEquiv (i, j)` of the tuple (`BitString.block`). Cutting a tuple into its blocks is an
equivalence `(Fin (m * k) → α) ≃ (Fin m → Fin k → α)` (`BitString.blocksEquiv`). The positions of
the blocks (`BitString.blockBits`) are pairwise disjoint, and gluing two tuples along the
positions of one block takes that block from the first tuple and every other block from the second
(`BitString.block_piecewise`).

## Main definitions

* `Cslib.BitString.block`: the `i`-th block of `k` entries of a tuple of `m * k` entries.
* `Cslib.BitString.blocksEquiv`: cutting a tuple into its blocks; its inverse reads entry `p` of
  the tuple in its block (`BitString.blocksEquiv_symm_apply`).
* `Cslib.BitString.blockBits`: the positions of the entries of a block.
* `Cslib.BitString.listBlock`: a block of a list (`BitString.listBlock_ofFn`).

## Main results

* `Cslib.BitString.pairwiseDisjoint_blockBits`: blocks occupy disjoint positions.
* `Cslib.BitString.block_piecewise`: gluing two tuples along one block.
-/

@[expose] public section

namespace Cslib.BitString

open Finset

variable {α : Type*} {m k : ℕ}

/-- The `i`-th block of `k` consecutive entries of a tuple of `m` blocks. -/
def block (x : Fin (m * k) → α) (i : Fin m) : Fin k → α :=
  fun j => x (finProdFinEquiv (i, j))

/-- Entry `j` of block `i` is entry `finProdFinEquiv (i, j)` of the tuple. -/
@[simp] theorem block_apply (x : Fin (m * k) → α) (i : Fin m) (j : Fin k) :
    block x i j = x (finProdFinEquiv (i, j)) :=
  rfl

/-- Cutting a tuple of `m * k` entries into its `m` blocks of `k` entries. This is definitionally
`(finProdFinEquiv.symm.arrowCongr (Equiv.refl α)).trans (Equiv.curry _ _ _)`. -/
@[simps symm_apply]
def blocksEquiv : (Fin (m * k) → α) ≃ (Fin m → Fin k → α) where
  toFun := block
  invFun y p := y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  left_inv x := funext fun p => by
    change x (finProdFinEquiv ((finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2)) = x p
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv y := funext fun i => funext fun j => by
    change y (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = y i j
    rw [Equiv.symm_apply_apply]

/-- `blocksEquiv` cuts a tuple into its blocks with `block`. -/
@[simp] theorem blocksEquiv_apply (x : Fin (m * k) → α) : blocksEquiv x = block x :=
  rfl

/-- Cutting the concatenation of blocks into its blocks recovers them. -/
@[simp] theorem block_blocksEquiv_symm (z : Fin m → Fin k → α) :
    block (blocksEquiv.symm z) = z :=
  blocksEquiv.apply_symm_apply z

/-- The positions of the bits of the `i`-th block of `k` bits. -/
def blockBits (k : ℕ) (i : Fin m) : Finset (Fin (m * k)) :=
  univ.filter fun p => (finProdFinEquiv.symm p).1 = i

/-- A position lies in block `i` exactly when its block index under `finProdFinEquiv` is `i`. -/
theorem mem_blockBits {i : Fin m} {p : Fin (m * k)} :
    p ∈ blockBits k i ↔ (finProdFinEquiv.symm p).1 = i := by
  simp [blockBits]

/-- Distinct blocks occupy disjoint positions. -/
theorem pairwiseDisjoint_blockBits (k : ℕ) :
    ((univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint (blockBits k) :=
  fun _ _ _ _ hij => disjoint_left.2 fun _ hi hj =>
    hij ((mem_filter.1 hi).2.symm.trans (mem_filter.1 hj).2)

/-- Gluing `x` and `z` along the positions of block `i` takes block `i` from `x` and the other
blocks from `z`. -/
theorem block_piecewise (i : Fin m) (x z : Fin (m * k) → α) (j : Fin m) :
    block ((blockBits k i).piecewise x z) j = if j = i then block x j else block z j := by
  funext b
  have hmem : finProdFinEquiv (j, b) ∈ blockBits k j := by simp [mem_blockBits]
  by_cases hj : j = i
  · subst hj
    simp only [block, ↓reduceIte, Finset.piecewise_eq_of_mem _ _ _ hmem]
  · have hmem' : finProdFinEquiv (j, b) ∉ blockBits k i := by simp [mem_blockBits, hj]
    simp only [block, hj, ↓reduceIte, Finset.piecewise_eq_of_notMem _ _ _ hmem']

/-- Block `i` of `k` entries of a list: the `k` entries from position `i * k` on. -/
def listBlock (k : ℕ) (z : List α) (i : ℕ) : List α := (z.drop (i * k)).take k

/-- Block `i` of the list of a tuple is the list of its block `i`. -/
theorem listBlock_ofFn (z : Fin (m * k) → α) (i : Fin m) :
    listBlock k (List.ofFn z) i = List.ofFn (block z i) := by
  have hi : (i + 1) * k ≤ m * k := Nat.mul_le_mul_right _ i.2
  refine List.ext_getElem (by
    simp only [listBlock, List.length_take, List.length_drop, List.length_ofFn]
    rw [Nat.add_mul] at hi
    omega) fun j h₁ h₂ => ?_
  simp only [listBlock, List.getElem_take, List.getElem_drop, List.getElem_ofFn, block_apply]
  congr 1
  ext
  simp only [finProdFinEquiv_apply_val]
  rw [Nat.mul_comm, Nat.add_comm]

end Cslib.BitString



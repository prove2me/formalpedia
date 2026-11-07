-- Prove2me | Definitions.Def_DynSort_Inv
-- name    : DynSort_Inv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:51.222715+00:00
-- url     : https://prove2.me/theorems/7aff49e4-c872-4e9e-9d4d-b18f69337758
-- title:
--   Structural invariants of a DST
-- statement:
--   For lists of elements, $A<B$ means that every element of $A$ is smaller than every element of $B$; comparisons involving an empty set are vacuous. A level-$i$ section satisfies the **structural invariants** when, recursively:
--
--   1. *Number and structure of blocks.* For $i\ge2$ it has one block $O$ or three blocks $O_1\mid T_2O_2\mid O_3$, all children of level $i-1$; the transfer section may be empty, but the original section of every middle block contains at least one element.
--   2. *Base-level sorting.* Every level-$1$ section is sorted in increasing order.
--   3. *Block sizes.* For a section of level-$j$ blocks ($j=i-1$): a single block has size at most $12\cdot2^j$; with three blocks, the middle block has size exactly $2^j$, the first block size in $[2^j,12\cdot2^j)$ and the last block size in $[7\cdot2^j,12\cdot2^j)$.
--   4. *Block ordering.* $O_1<O_2<T_2$ and $O_2<O_3$. If $O_3$ is a level-$1$ section, also $T_2<O_3$; otherwise, writing $O_3=O_1'\mid T_2'O_2'\mid O_3'$, also $O_1'<T_2<O_2'$.
--
--   The **loose** invariants drop only the requirement that each middle original section contains an element. A **root** of level $i$ satisfies the invariants, has at most one hole, and has at most $24\cdot2^{i-1}$ cells, the capacity within which the paper's rebuilding rule constructs a valid level-$i$ DST. The module also defines when a three-block section has a nonempty middle original section.
--
--   **Formalization Note** The hole counts in sizes and is ignored in comparisons. Level-$1$ sorting is strict, since elements are distinct. When $i\ge3$ the size bounds force $O_3$ to have three blocks, so the ordering clause for a single-block $O_3$ never applies and is read as true.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), §4.2, pp.11–12 (PDF pp.13–14); capacity, Proof of Claim 23, p.54 (PDF p.56)

import Mathlib
import Definitions.Def_DynSort_Sec

namespace DynSort

/-! # The structural invariants of a DST

Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §4.2, pp.11–12 (PDF pp.13–14); capacity of a
root, Proof of Claim 23, p.54 (PDF p.56).

`A < B` means every element of `A` is smaller than every element of `B`; comparisons involving an
empty set are vacuous. For a level-`i` section:
1. *Number and Structure of Blocks.* For `i ≥ 2`, one block `O` or three blocks `O₁ | T₂ O₂ | O₃`;
   the transfer section may be empty, but the original section of every middle block contains at
   least one element.
2. *Base-Level Sorting.* Every level-1 section is sorted in increasing order.
3. *Block Sizes.* For a section of level-`j` blocks (`j = i − 1`): a single block has size at most
   `12·2^j`; with three blocks the middle block has size exactly `2^j`, the first block size in
   `[2^j, 12·2^j)` and the last block size in `[7·2^j, 12·2^j)`.
4. *Block Ordering.* `O₁ < O₂ < T₂` and `O₂ < O₃`. If `O₃` is a level-1 section, also `T₂ < O₃`;
   otherwise, writing `O₃ = O′₁ | T′₂ O′₂ | O′₃`, `O′₁ < T₂ < O′₂`.

**Formalization Note.**
* `InvGen strict i S` is the recursive conjunction of 1–4 at level `i`; `Inv := InvGen true`.
  `InvLoose := InvGen false` drops only "the original section of every middle block contains at
  least one element"; it describes the state just before a SwapHole whose middle original section
  may have lost its last element.
* The hole counts in sizes and is ignored in comparisons (pp.12, 14). Level-1 sorted is strictly
  increasing on the stored cells (elements are distinct, p.11).
* `O₃` of a level-`i` three-block section with `i ≥ 3` is three-block by the size bounds (p.12), so
  the ordering clause for a `single` last section is `True`; it never applies.
* `RootInv i S` adds, for a root (an A-DST component, or a section considered on its own), at most
  one hole and the capacity `S.size ≤ 24·2^{i−1}` of p.54. Every section of a DST and every A-DST
  component meets it.
-/

variable {α : Type}

/-- `A < B` for lists of elements: every element of `A` is smaller than every element of `B`. -/
def SecLt [LT α] (A B : List α) : Prop := ∀ a ∈ A, ∀ b ∈ B, a < b

/-- The terminal ordering of a three-block section with transfer section `T2` and last original
section `O3` (p.12): `T₂ < O₃` when `O₃` is level 1, `O′₁ < T₂ < O′₂` when it has three blocks. -/
def terminalOrder [LT α] (T2 O3 : Sec α) : Prop :=
  match O3 with
  | .leaf _ => SecLt T2.stored O3.stored
  | .three O1' _ O2' _ => SecLt O1'.stored T2.stored ∧ SecLt T2.stored O2'.stored
  | .single _ => True

/-- The four structural invariants of §4.2 for a level-`i` section, recursively; with
`strict = false` the condition that a middle original section has an element is dropped. -/
def InvGen [LinearOrder α] (strict : Bool) : ℕ → Sec α → Prop
  | 1, .leaf c => (c.filterMap id).Pairwise (· < ·)
  | L + 2, .single O => InvGen strict (L + 1) O ∧ O.size ≤ 12 * 2 ^ (L + 1)
  | L + 2, .three O1 T2 O2 O3 =>
      InvGen strict (L + 1) O1 ∧ InvGen strict (L + 1) T2 ∧
      InvGen strict (L + 1) O2 ∧ InvGen strict (L + 1) O3 ∧
      (strict = true → O2.stored ≠ []) ∧
      T2.size + O2.size = 2 ^ (L + 1) ∧
      2 ^ (L + 1) ≤ O1.size ∧ O1.size < 12 * 2 ^ (L + 1) ∧
      7 * 2 ^ (L + 1) ≤ O3.size ∧ O3.size < 12 * 2 ^ (L + 1) ∧
      SecLt O1.stored O2.stored ∧ SecLt O2.stored T2.stored ∧ SecLt O2.stored O3.stored ∧
      terminalOrder T2 O3
  | _, _ => False

/-- **The structural invariants of a level-`i` DST** (§4.2, pp.11–12). -/
def Inv [LinearOrder α] (i : ℕ) (S : Sec α) : Prop := InvGen true i S

/-- The structural invariants without "the original section of every middle block contains at
least one element". -/
def InvLoose [LinearOrder α] (i : ℕ) (S : Sec α) : Prop := InvGen false i S

/-- **A level-`i` root**: the invariants, at most one hole, and the capacity `24·2^{i−1}` (p.54). -/
def RootInv [LinearOrder α] (i : ℕ) (S : Sec α) : Prop :=
  Inv i S ∧ S.size ≤ 24 * 2 ^ (i - 1) ∧ S.holes ≤ 1

/-- A three-block section whose middle original section stores an element (other shapes: `True`). -/
def midNonempty : Sec α → Prop
  | .three _ _ O2 _ => O2.stored ≠ []
  | _ => True

end DynSort



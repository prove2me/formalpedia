-- Prove2me | Definitions.Def_ExactOneHS_Counting_Instance
-- name    : ExactOneHS_Counting_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:11:26.584196+00:00
-- url     : https://prove2.me/theorems/e2d1e487-96dd-4857-be8d-d1e52b57f962
-- title:
--   Exact-One Hitting Set instances on $[r]$, the count $Z(U,F)$, the rational incidence system $Ax = 1$ and its augmented row bases
-- statement:
--   An **Exact-One Hitting Set instance** consists of a declared ground set $U = [r]$ of $r$ elements and an explicitly listed family $F = (S_1, \dots, S_m)$ of subsets of $U$; the family may contain repeated sets and may be empty, and $r = 0$ is allowed. A set $W \subseteq U$ is an **exact-one hitting set** if it meets every listed set exactly once,
--   $$|W \cap S| = 1 \quad \text{for every } S \in F,$$
--   and $\mathrm{Sol}(U, F)$ is the set of all such $W$. The **count** is
--   $$Z(U, F) = |\mathrm{Sol}(U, F)| \in \{0, 1, \dots, 2^r\}.$$
--   An empty family gives $Z = 2^r$, and a family containing the empty set gives $Z = 0$.
--
--   The **incidence matrix** $A \in \mathbb{Q}^{m \times r}$ has $A_{ji} = 1$ if $i \in S_j$ and $0$ otherwise; identifying $W$ with its indicator vector $x \in \{0,1\}^r$, the exact-one conditions read $Ax = \mathbf 1$. The system is **consistent** if it has a rational solution $x \in \mathbb{Q}^r$, and $\operatorname{rank} A$ is the rank over $\mathbb{Q}$. The **direct cases** are: $r \le 1$, $F$ empty, $\emptyset \in F$, $Ax = \mathbf 1$ inconsistent, or $\operatorname{rank} A = r$. The **augmented matrix** is $(A \mid \mathbf 1)$, and a set $s$ of row indices is an **augmented row basis** if the rows of $(A \mid \mathbf 1)$ indexed by $s$ are linearly independent and span the row space of $(A \mid \mathbf 1)$; the **retained sets** are the $S_j$ with $j \in s$, in their original order.
--
--   An instance is coded as a bit string by writing $r$ in unary and then the list of sets, each set as the increasing list of its element indices, each index in unary, in the self-delimiting list format of `SubexponentialSAT`.
--
--   **Formalization Note.** Elements are `Fin r` (indices $0, \dots, r-1$ for the paper's $1, \dots, r$), the family is a `List` (so repeated sets are kept and $A$ has one row per listed set), rows of $A$ are indexed by `Fin m` with $m$ the length of the list, $\operatorname{rank}$ is `Matrix.rank` over `ℚ`, and the extra column of $(A \mid \mathbf 1)$ is indexed by `Unit`.
-- source:
--   Chen, Jiang, Zhu, Counting Exact-One Hitting Sets in Subexponential Time, STOC 2027 submission (manuscript sha256 4b9a238a…), p. 3, Eqs. (1), (2); p. 10, §3 Conventions and Eq. (8); p. 5, Theorem 1.2 (direct cases); p. 15, proof of Theorem 1.2 (incidence matrix, augmented row space)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_QAlgorithms_ClassicalStringComputability

namespace ExactOneHS.Counting

open OAI.Algorithms.SubexponentialSAT

/-- An Exact-One Hitting Set instance `([r], F)`: the declared ground set is `Fin r` (the paper's
`[r] = {1, …, r}`, indexed from `0`), and the family `F` is an explicit list of subsets of it;
repeated sets are allowed. -/
structure Instance where
  /-- the number `r` of declared elements -/
  r : ℕ
  /-- the explicitly listed family `F = (S_1, …, S_m)` -/
  family : List (Finset (Fin r))

namespace Instance

variable (I : Instance)

/-- `W ⊆ [r]` is an exact-one hitting set: `|W ∩ S| = 1` for every listed `S` (Eq. (1)). -/
def IsSolution (W : Finset (Fin I.r)) : Prop :=
  ∀ S ∈ I.family, (W ∩ S).card = 1

instance : DecidablePred I.IsSolution := fun W => by
  unfold IsSolution; infer_instance

/-- `Sol(U, F)`, the set of all exact-one hitting sets. -/
def sol : Finset (Finset (Fin I.r)) :=
  Finset.univ.filter I.IsSolution

/-- `Z(U, F) = # Sol(U, F)` (Eq. (2)). -/
def Z : ℕ := I.sol.card

/-- The incidence matrix `A` over `ℚ`: row `j` is the indicator vector of the `j`-th listed set,
`A_{j i} = 1` if `i ∈ S_j` and `0` otherwise, so that Eq. (8) reads `A x = 1`. -/
def incidence : Matrix (Fin I.family.length) (Fin I.r) ℚ :=
  fun j i => if i ∈ I.family.get j then 1 else 0

/-- The rational incidence system `A x = 1` is consistent: it has a rational solution. -/
def IsConsistent : Prop :=
  ∃ x : Fin I.r → ℚ, Matrix.mulVec I.incidence x = fun _ => 1

/-- The direct cases of Theorem 1.2: `r ≤ 1`, `F` empty, `∅ ∈ F`, `A x = 1` inconsistent over
`ℚ`, or `A` of full column rank (`rank A = r` over `ℚ`). -/
def IsDirectCase : Prop :=
  I.r ≤ 1 ∨ I.family = [] ∨ ∅ ∈ I.family ∨ ¬ I.IsConsistent ∨ I.incidence.rank = I.r

/-- The augmented matrix `(A | 1)` over `ℚ`, the extra column indexed by `Unit`. -/
def augmented : Matrix (Fin I.family.length) (Fin I.r ⊕ Unit) ℚ :=
  Matrix.fromCols I.incidence (fun _ _ => 1)

/-- The rows indexed by `s` are original rows forming a basis of the row space of `(A | 1)`. -/
def IsAugmentedRowBasis (s : Finset (Fin I.family.length)) : Prop :=
  LinearIndependent ℚ (fun j : s => I.augmented j) ∧
    Submodule.span ℚ (I.augmented '' (s : Set (Fin I.family.length))) =
      Submodule.span ℚ (Set.range I.augmented)

/-- The retained sets `S_j` (`j ∈ s`), in their original order. -/
def retained (s : Finset (Fin I.family.length)) : List (Finset (Fin I.r)) :=
  ((List.finRange I.family.length).filter (fun j => decide (j ∈ s))).map I.family.get

end Instance

/-- Code of a set of elements: its elements as natural numbers in increasing order, each in
unary, as a self-delimiting list. -/
def encodeElementSet {r : ℕ} (S : Finset (Fin r)) : List Bool :=
  Encoding.encodeList Encoding.encodeNat ((S.image Fin.val).sort (· ≤ ·))

/-- Code of an instance: `r` in unary, then the list of sets (repetitions kept). -/
def encodeInstance (I : Instance) : List Bool :=
  QAlgorithms.Complexity.encNat I.r ++ Encoding.encodeList encodeElementSet I.family

end ExactOneHS.Counting



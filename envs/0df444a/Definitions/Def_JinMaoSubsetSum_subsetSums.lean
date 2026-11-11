-- Prove2me | Definitions.Def_JinMaoSubsetSum_subsetSums
-- name    : JinMaoSubsetSum_subsetSums
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:38:06.830861+00:00
-- url     : https://prove2.me/theorems/e20c8885-108b-4cf0-ba60-be30819ba56a
-- title:
--   Subset sums $\Sigma(A)$ of a multiset and the pair-list representation of multisets
-- statement:
--   A finite **multiset** $A$ is a function $\mu_A$ giving each element $x$ a multiplicity $\mu_A(x)\ge 0$, with finite support $\operatorname{supp}A=\{x:\mu_A(x)>0\}$; its size is $|A|=\sum_x\mu_A(x)$, and $B\subseteq A$ means $\mu_B\le\mu_A$. The paper represents $A$ by the list of pairs $(x,\mu_A(x))$ over $x\in\operatorname{supp}A$. The **set of subset sums** of $A$ is
--   $$
--   \Sigma(A)=\Bigl\{\sum_{b\in B}b \;:\; B\subseteq A\Bigr\},
--   $$
--   where sums run over sub-multisets with multiplicity and the empty sub-multiset gives $0$.
--
--   Every algorithmic statement of the mission reads multisets as such pair lists. A list $l=((x_1,\mu_1),\dots,(x_L,\mu_L))$ represents $A$ when the $x_j$ are distinct, every $\mu_j$ is positive, and the multiset listed is $A$; the order of the list is arbitrary. A sub-multiset of $A$ is then given by multiplicities $\beta_j\le\mu_j$ aligned with the list, and its sum is $\sum_j\beta_jx_j$.
--
--   **Formalization Note** Multisets are Mathlib's `Multiset`; `subsetSums` is $\Sigma(A)$ and `subsetSumsFinset` the same finite set as a `Finset`. `IsPairRep`, `AlignedLe`, `subOfPairs`, `alignedSum` express the pair-list representation and aligned sub-multisets. `pairsWords` and `vpairsWords` are the integer sequences written into memory for a pair list: its length, then each element (a vector coordinate by coordinate) followed by its multiplicity.
-- source:
--   Jin, Mao, Subset Sum in Almost-Linear Time, arXiv:2610.20742v1 (sha256 8b604948862d9188e922b8abf95831fde3a3699e26d39177d20a1460e31a926a), §3.1, p.15 (PDF p.17)

import Mathlib

set_option autoImplicit false

namespace JinMaoSubsetSum

/-!
# Multisets, their pair-list representation, and subset sums

Jin, Mao, *Subset Sum in Almost-Linear Time*, arXiv:2610.20742v1, §3.1, p.15: "A (finite)
multiset A is represented by a list of pairs of element x together with its multiplicity µ_A(x),
over all x ∈ supp A := {x : µ_A(x) > 0}. Its size is |A| = Σ_x µ_A(x). [...] The set of subset
sums of a (multi)set A is Σ(A) = {Σ_{b∈B} b : B ⊆ A}."

**Formalization Note.**
* A multiset is Mathlib's `Multiset α`; `B ≤ A` is the sub-multiset relation `µ_B ≤ µ_A`,
  `A + B` is the multiset union `A ⊔ B` of the paper (`µ_{A⊔B} = µ_A + µ_B`), and
  `Multiset.card A` is the size `|A|`.
* A list of pairs `l` represents `A` (`IsPairRep l A`) when its first components are distinct,
  every multiplicity is positive, and the multiset it lists is `A`. The order of the list is not
  fixed by the paper; every statement that reads a multiset from memory quantifies over all orders.
* A sub-multiset of the multiset listed by `l` is written by a list `β` of multiplicities aligned
  with `l` (`AlignedLe l β`: same length, `β_j ≤ µ_j`); it is the multiset `subOfPairs l β` and its
  sum is `alignedSum l β`.
* `pairsWords l` and `vpairsWords l` are the integer sequences written into memory for a list of
  pairs: the number of pairs, then each element (a vector coordinate by coordinate, coordinate `0`
  first) followed by its multiplicity.
-/

/-- `Σ(A)`: the set of sums `Σ_{b ∈ B} b` of all sub-multisets `B ⊆ A` (the empty sub-multiset
gives `0`). -/
def subsetSums {α : Type*} [AddCommMonoid α] (A : Multiset α) : Set α :=
  {s | ∃ B : Multiset α, B ≤ A ∧ B.sum = s}

/-- The finite set `Σ(A)` as a `Finset` (the image of the sum over all sub-multisets). -/
def subsetSumsFinset {α : Type*} [AddCommMonoid α] [DecidableEq α] (A : Multiset α) : Finset α :=
  (A.powerset.map Multiset.sum).toFinset

/-- The multiset listed by a list of (element, multiplicity) pairs. -/
def ofPairs {α : Type*} (l : List (α × ℕ)) : Multiset α :=
  (l.map (fun p => Multiset.replicate p.2 p.1)).sum

/-- The paper's representation of a multiset: distinct elements, positive multiplicities. -/
def IsPairRep {α : Type*} (l : List (α × ℕ)) (A : Multiset α) : Prop :=
  (l.map Prod.fst).Nodup ∧ (∀ p ∈ l, 0 < p.2) ∧ ofPairs l = A

/-- `β` is a list of multiplicities aligned with `l`, below those of `l`. -/
def AlignedLe {α : Type*} (l : List (α × ℕ)) (β : List ℕ) : Prop :=
  List.Forall₂ (fun b p => b ≤ p.2) β l

/-- The sub-multiset of `ofPairs l` with multiplicities `β` (aligned with `l`). -/
def subOfPairs {α : Type*} (l : List (α × ℕ)) (β : List ℕ) : Multiset α :=
  (List.zipWith (fun p b => Multiset.replicate b p.1) l β).sum

/-- The sum `Σ_j β_j · x_j` of the sub-multiset with multiplicities `β` aligned with `l`. -/
def alignedSum {M : Type*} [AddCommMonoid M] (l : List (M × ℕ)) (β : List ℕ) : M :=
  (List.zipWith (fun p b => b • p.1) l β).sum

/-- Memory layout of a list of integer pairs: `|l|`, then `x₁, µ₁, x₂, µ₂, …`. -/
def pairsWords (l : List (ℤ × ℕ)) : List ℤ :=
  (l.length : ℤ) :: l.flatMap (fun p => [p.1, (p.2 : ℤ)])

/-- Memory layout of a list of (integer vector, multiplicity) pairs: `|l|`, then for each pair the
`d` coordinates of the vector (coordinate `0` first) followed by the multiplicity. -/
def vpairsWords {d : ℕ} (l : List ((Fin d → ℤ) × ℕ)) : List ℤ :=
  (l.length : ℤ) :: l.flatMap (fun p => List.ofFn p.1 ++ [(p.2 : ℤ)])

end JinMaoSubsetSum



-- Prove2me | Definitions.Def_FewInnerTSP_RankReduction
-- name    : FewInnerTSP_RankReduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:32:02.0452+00:00
-- url     : https://prove2.me/theorems/3457598b-6d86-4ee4-b08c-b55bcaaa604b
-- title:
--   Cut rows over GF(2) and the weighted rank reduction of App. C.1
-- statement:
--   Let $B$ be a terminal set with root $r=\min B$. The **cut row** $z_M$ of a matching $M$ on $B$ is the vector over $\mathrm{GF}(2)$ indexed by the subsets $T\subseteq B\setminus\{r\}$ (the right sides of the $2^{b-1}$ cuts with the root on the left), with entry $1$ exactly when no pair of $M$ is split by the cut.
--
--   The **weighted rank reduction** of a finite family of covers of a state sorts the covers by nondecreasing weight, ties broken by a fixed injective tie rule, and scans them, retaining a cover when the cut row of its matching is linearly independent of the rows of the covers retained so far.
--
--   This is the compression step of Lemma 5.2, used in the base case and after every join of Algorithm 2.
--
--   **Formalization Note** The page fixes no particular tie rule, so it is a parameter.
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), App. C.1, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_FewInnerTSP_State

namespace FewInnerTSP

open Classical in
/-- **The cut row** `z_M` of a matching `M` on `B`, as a vector over `GF(2)` indexed by the subsets `T`
of `B`. The columns are the `2^{b-1}` cuts of `B` with the root (the least element of `B`) on the left,
that is `T ⊆ B` without the root, `T` being the right side. The entry is `1` exactly when no pair of `M`
is split by the cut; it is `0` off these columns.
Source: Li, Ma, Gong, STOC 2027 submission (manuscript sha256 6541f631…), App. C.1, p.19 (PDF p.21). -/
noncomputable def cutRow {n : ℕ} (B : Finset (Fin n)) (M : Finset (Sym2 (Fin n))) :
    Finset (Fin n) → ZMod 2 :=
  fun T =>
    if T ⊆ B ∧ (∀ r ∈ B, (∀ x ∈ B, r ≤ x) → r ∉ T) ∧
        ∀ a b, s(a, b) ∈ M → (a ∈ T ↔ b ∈ T)
    then 1 else 0

open Classical in
/-- Greedy basis extraction: scan the list and retain an element when its row is independent of the
rows of the previously retained elements. Source: Li, Ma, Gong, App. C.1, p.19 (PDF p.21). -/
noncomputable def greedyBasis {α ι : Type*} (row : α → (ι → ZMod 2)) (L : List α) : List α :=
  L.foldl (fun kept c =>
    if row c ∈ Submodule.span (ZMod 2) ((fun x => row x) '' {x | x ∈ kept}) then kept
    else kept ++ [c]) []

open Classical in
/-- **The weighted rank reduction** of a finite family of covers of the state `S`: sort by nondecreasing
weight, using the fixed tie rule `tie`, and retain a cover when its cut row is independent of the
previously retained rows.
Source: Li, Ma, Gong, App. C.1, p.19 (PDF p.21): "Sort covers by nondecreasing weight, using a fixed tie
rule, and retain a row when it is independent of the previously retained rows."

**Formalization Note** The paper fixes no particular tie rule, so `tie` is a parameter, an injection
from edge sets to `ℕ`; with an injective `tie` the sorted order of a family is unique. -/
noncomputable def rankReduce {n m : ℕ} (Γ : Skeleton n m) (S : State n m)
    (tie : Finset (Edge n m) → ℕ) (𝒜 : Finset (Finset (Edge n m))) :
    Finset (Finset (Edge n m)) :=
  (greedyBasis (fun C => cutRow S.B (matchingOf Γ S C))
    (𝒜.toList.insertionSort fun C D =>
      S.wtOf C < S.wtOf D ∨ (S.wtOf C = S.wtOf D ∧ tie C ≤ tie D))).toFinset

end FewInnerTSP



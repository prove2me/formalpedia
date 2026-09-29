-- Prove2me | Definitions.Def_BinPacking_SmallItems_Weight
-- name    : BinPacking_SmallItems_Weight
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:19:38.50765+00:00
-- url     : https://prove2.me/theorems/b3ed55fc-011b-45be-a6b8-441db1e91ba0
-- title:
--   The weighting function $W$ of Section 4: $k$-pieces, $w_1$, relation $k$, $w_2$, $w_{12}(\pi)$, $W(X)$, and BASIC/SURPLUS
-- statement:
--   These are the weighting objects of Section 4 of Johnson et al. (1974), used to analyse First-Fit Decreasing on lists with no element exceeding $1/2$.
--
--   1. For an integer $k\ge 1$, a number $x$ is a **$k$-piece** if $x\in\bigl(\tfrac1{k+1},\tfrac1k\bigr]$. A **$k$-bin** of a packing is a bin whose largest element is a $k$-piece.
--   2. The single-element weight is $w_1(x)=\lfloor 1/x\rfloor^{-1}$, so $w_1(x)=1/k$ when $x$ is a $k$-piece.
--   3. A pair $(x,y)$ **obeys relation $k$** if $x$ is a $k$-piece and $kx+y\le 1$. The pair weight is
--   $$w_2(x,y)=\begin{cases} w_1(x)+\dfrac{k-1}{k}\,w_1(y) & \text{if }(x,y)\text{ obeys relation }k,\\[4pt] w_1(x)+w_1(y) & \text{otherwise,}\end{cases}$$
--   where $k$ is the piece type of the first element $x$.
--   4. For a partition $\pi$ of a set $X$ of elements into one- and two-element sets, let $\pi(1)$ be the elements in one-element sets and $\pi(2)$ the pairs $(x,y)$ with $\{x,y\}\in\pi$ and $\operatorname{index}(x)<\operatorname{index}(y)$, where the elements are indexed in nonincreasing order. Then
--   $$w_{12}(\pi)=\sum_{x\in\pi(1)}w_1(x)+\sum_{(x,y)\in\pi(2)}w_2(x,y),\qquad W(X)=\min_{\pi} w_{12}(\pi),$$
--   the minimum over all partitions of $X$ into one- and two-element sets.
--   5. For a list $L$, **BASIC** is the set of elements $x$ such that, for some $k$, $x$ is a $k$-piece and lies in a $k$-bin of the FFD packing of $L$; **SURPLUS** is the rest of $L$.
--
--   The weight $W$ charges each element of a list by its size class, and discounts the second element of a pair that fits together in a way characteristic of FFD packings. It is the tool by which the $71/60$ bound for FFD is proved.
--
--   **Formalization Note** $W$ is defined on `X : List ℝ` by rearranging $X$ into nonincreasing order (`sortDesc`) and indexing by positions; each pair is therefore oriented (larger, smaller), and for equal values the orientation does not change $w_2$, so $W$ depends only on the multiset of values. A partition into one- and two-element sets is an involution `σ` of the positions (`σ * σ = 1`): fixed points are singletons and each pair $\{i,\sigma(i)\}$ with $i<\sigma(i)$ is a two-element set. The minimum is `Finset.inf'` over the finite nonempty set of involutions (the identity is one), so it is attained and never a junk value. The integer $k$ in $w_2$ is $\lfloor 1/x\rfloor$, which for $x\in(0,1]$ is the unique $k$ with $x$ a $k$-piece. BASIC and SURPLUS are sets of positions of `sortDesc L`; the bin of a position is its bin in the final FFD packing, and the largest element of a bin is computed as a maximum with $0$ (bins are nonempty and elements positive). Values are real; the paper's rational codomain is incidental.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), pp. 315-317, Section 4 (definitions of W, pi(1), pi(2), w_12, k-piece, k-bin, w_1, BASIC, SURPLUS, relation k, w_2)

import Mathlib
import Definitions.Def_BinPacking_SmallItems_Model

namespace BinPacking.SmallItems

open Classical

/-- `x` is a `k`-piece (p. 316) if `x ∈ (1/(k + 1), 1/k]`. (For `k = 0` no real is a `0`-piece,
since `1/0 = 0` in Lean.) -/
def IsPiece (k : ℕ) (x : ℝ) : Prop := 1 / ((k : ℝ) + 1) < x ∧ x ≤ 1 / (k : ℝ)

/-- `w₁(x) = ⌊1/x⌋⁻¹` (p. 316). For `x ∈ (0, 1]` the integer `⌊1/x⌋` is the unique `k` with `x` a
`k`-piece, so `w₁(x) = 1/k`. -/
noncomputable def w1 (x : ℝ) : ℝ := ((⌊1 / x⌋₊ : ℕ) : ℝ)⁻¹

/-- `(x, y)` obeys relation `k` (p. 317) if `x` is a `k`-piece and `kx + y ≤ 1`. -/
def ObeysRelation (k : ℕ) (x y : ℝ) : Prop := IsPiece k x ∧ (k : ℝ) * x + y ≤ 1

/-- `w₂(x, y)` (p. 317): `w₁(x) + ((k − 1)/k) w₁(y)` if `(x, y)` obeys relation `k`, where `k` is
the piece type of `x`, and `w₁(x) + w₁(y)` otherwise. The relation uses the `k` of the first
(larger) element `x`; for `x ∈ (0, 1]` that `k` is `⌊1/x⌋`. -/
noncomputable def w2 (x y : ℝ) : ℝ :=
  if ObeysRelation ⌊1 / x⌋₊ x y then
    w1 x + (((⌊1 / x⌋₊ : ℕ) : ℝ) - 1) / ((⌊1 / x⌋₊ : ℕ) : ℝ) * w1 y
  else w1 x + w1 y

/-- The partitions of the positions `0, …, n - 1` into one- and two-element sets, encoded as the
involutions `σ` of `Fin n` (`σ * σ = 1`): the fixed points are the one-element sets and the
pairs `{i, σ i}` with `i ≠ σ i` the two-element sets. The set is finite and contains `σ = 1`. -/
noncomputable def pairings (n : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => σ * σ = 1)

/-- `w₁₂(π)` (p. 316) for a partition `π` (an involution `σ`) of the positions of a list `S`:
`Σ_{x ∈ π(1)} w₁(x) + Σ_{(x,y) ∈ π(2)} w₂(x, y)`, where `π(1)` are the fixed points and `π(2)`
the pairs `(S_i, S_{σ i})` with `i < σ i` (the paper's `index(x) < index(y)`). -/
noncomputable def w12 (S : List ℝ) (σ : Equiv.Perm (Fin S.length)) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i => σ i = i), w1 (S.get i)) +
    ∑ i ∈ Finset.univ.filter (fun i => i < σ i), w2 (S.get i) (S.get (σ i))

/-- The weight `W(X) = min_π w₁₂(π)` (pp. 315–316), `π` ranging over all partitions of `X` into
one- and two-element sets. The elements are indexed in nonincreasing order (the paper's `L` is in
decreasing order), so each pair is oriented (larger, smaller); for equal values the orientation
does not affect `w₂`, and `W` depends only on the multiset `X`. The minimum is over the finite
nonempty set `pairings`, so it is attained. -/
noncomputable def W (X : List ℝ) : ℝ :=
  (pairings (sortDesc X).length).inf' ⟨1, by simp [pairings]⟩ (w12 (sortDesc X))

/-- The largest element of a bin (`0` for an empty bin; every bin of a packing is nonempty). -/
def binMax (B : List ℝ) : ℝ := B.foldr max 0

/-- A `k`-bin (p. 316): a bin whose largest element is a `k`-piece. -/
def IsKBin (k : ℕ) (B : List ℝ) : Prop := IsPiece k (binMax B)

/-- The final FFD bin (in `ffdPack L`) holding position `i` of the sorted list `sortDesc L`. -/
noncomputable def ffdBin (L : List ℝ) (i : Fin (sortDesc L).length) : List ℝ :=
  (ffdPack L).getD (ffBinOf (sortDesc L) i) []

/-- BASIC (p. 316): the positions `i` of the sorted list `sortDesc L` such that, for some `k`,
the item is a `k`-piece and lies in a `k`-bin of the FFD packing of `L`. -/
noncomputable def basic (L : List ℝ) : Finset (Fin (sortDesc L).length) :=
  Finset.univ.filter (fun i => ∃ k : ℕ, IsPiece k ((sortDesc L).get i) ∧ IsKBin k (ffdBin L i))

/-- SURPLUS `= L − BASIC` (p. 317), as positions of the sorted list. -/
noncomputable def surplus (L : List ℝ) : Finset (Fin (sortDesc L).length) :=
  Finset.univ \ basic L

end BinPacking.SmallItems



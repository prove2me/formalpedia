-- Prove2me | Definitions.Def_BinPacking_Decreasing_Weight
-- name    : BinPacking_Decreasing_Weight
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:14:14.755149+00:00
-- url     : https://prove2.me/theorems/3e393f3e-3e6e-41f3-ba28-e2edaf144b62
-- title:
--   The weighting function $W$ of Section 4: $w_1$, the discounting relations, $w_2$ and $W(X)=\min_\pi w_{12}(\pi)$
-- statement:
--   This file defines the set weighting function $W$ that Johnson, Demers, Ullman, Garey and Graham use for their First-Fit Decreasing upper bounds.
--
--   An element $x$ is a **$k$-piece** if $x\in\bigl(\tfrac1{k+1},\tfrac1k\bigr]$, so for $0<x\le 1$ the index is $k=\lfloor 1/x\rfloor$. The single-element weight is
--   $$w_1(x)=\lfloor 1/x\rfloor^{-1},$$
--   that is, $w_1(x)=1/k$ for a $k$-piece. A pair $(x,y)$ **obeys relation $k$** if $x$ is a $k$-piece and $kx+y\le 1$. The pair weight is
--   $$w_2(x,y)=\begin{cases} w_1(x)+\dfrac{k-1}{k}\,w_1(y) & \text{if }(x,y)\text{ obeys relation }k,\\[4pt] w_1(x)+w_1(y) & \text{otherwise.}\end{cases}$$
--
--   For a finite collection $X$ of elements listed in nonincreasing order, and a partition $\pi$ of $X$ into one- and two-element sets, let $\pi(1)$ be the elements in singletons and $\pi(2)$ the pairs $(x,y)$ with $\operatorname{index}(x)<\operatorname{index}(y)$. Then
--   $$w_{12}(\pi)=\sum_{x\in\pi(1)}w_1(x)+\sum_{(x,y)\in\pi(2)}w_2(x,y),\qquad W(X)=\min_\pi w_{12}(\pi),$$
--   the minimum over all such partitions (a finite, nonempty family: the partition into singletons is one of them).
--
--   $W$ is the weight whose total over the list is compared with the number of FFD bins in Lemma 4.2.
--
--   **Formalization Note** `X : List ℝ` is first arranged into nonincreasing order by `sortDesc` (the mission's stable merge sort), and `index` is the position in that order, so every pair is oriented (larger, smaller) as in the paper's proofs, where $L$ is in decreasing order; for equal values the orientation does not change $w_2$, so $W$ depends only on the multiset of values. A partition of the positions $\{0,\dots,n-1\}$ into one- and two-element sets is encoded as an involution `m` of `Fin n` (singletons are fixed points, pairs are $\{i, m\,i\}$), and each pair is counted once, from its smaller position. The minimum is `Finset.inf'` over the nonempty finite set of involutions. Values are real rather than rational. $w_1$ uses `Int.floor`; it is only meaningful for $0<x\le 1$, which every statement assumes.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), pp. 315-317, Section 4 (definition of W, w₁₂, k-pieces, w₁, relation k, w₂)

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model

namespace BinPacking.Decreasing

/-- The piece number of `x` (p. 316): `x` is a `k`-piece when `x ∈ (1/(k+1), 1/k]`, i.e.
`k = ⌊1/x⌋`. Meaningful for `0 < x ≤ 1` (then `k ≥ 1`). -/
noncomputable def pieceNum (x : ℝ) : ℤ := ⌊1 / x⌋

/-- `w₁(x) = ⌊1/x⌋⁻¹` (p. 316); for a `k`-piece, `w₁(x) = 1/k`. -/
noncomputable def w1 (x : ℝ) : ℝ := ((pieceNum x : ℝ))⁻¹

/-- `(x, y)` obeys relation `k` (p. 317): `x` is a `k`-piece and `k x + y ≤ 1`. Since the piece
number of `x` is unique, this is `⌊1/x⌋ · x + y ≤ 1`. -/
abbrev ObeysRelation (x y : ℝ) : Prop := (pieceNum x : ℝ) * x + y ≤ 1

/-- `w₂(x, y)` (p. 317): `w₁(x) + ((k − 1)/k) w₁(y)` if `(x, y)` obeys relation `k`,
and `w₁(x) + w₁(y)` otherwise. -/
noncomputable def w2 (x y : ℝ) : ℝ :=
  if ObeysRelation x y then w1 x + ((pieceNum x : ℝ) - 1) / (pieceNum x : ℝ) * w1 y
  else w1 x + w1 y

/-- The partitions of the positions `{0, …, n − 1}` into one- and two-element sets, encoded as
involutions `m` of `Fin n`: `i` is a singleton when `m i = i`, and `{i, m i}` is a pair
otherwise. The identity (all singletons) is always one of them. -/
def partitions (n : ℕ) : Finset (Fin n → Fin n) :=
  Finset.univ.filter (fun m => ∀ i, m (m i) = i)

/-- `w₁₂(π)` (p. 316) for the partition `m` of the positions of the list `S`: the sum of `w₁(x)`
over singletons `{x}` plus the sum of `w₂(x, y)` over pairs `{x, y}` with `index(x) < index(y)`
(each pair is counted once, from its smaller position). -/
noncomputable def w12 (S : List ℝ) (m : Fin S.length → Fin S.length) : ℝ :=
  ∑ i : Fin S.length,
    if m i = i then w1 (S.get i)
    else if i < m i then w2 (S.get i) (S.get (m i)) else 0

/-- The weight `W(X)` (pp. 315–316): `X` is arranged into nonincreasing order (`sortDesc`), so
that `index` is the position in that order and every pair `(x, y)` with `index(x) < index(y)`
has `x ≥ y`; then `W(X) = min_π w₁₂(π)` over all partitions `π` of the positions into one- and
two-element sets (a finite nonempty family). -/
noncomputable def W (X : List ℝ) : ℝ :=
  (partitions (sortDesc X).length).inf' ⟨id, by simp [partitions]⟩ (w12 (sortDesc X))

end BinPacking.Decreasing



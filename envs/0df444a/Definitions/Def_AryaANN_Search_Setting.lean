-- Prove2me | Definitions.Def_AryaANN_Search_Setting
-- name    : AryaANN_Search_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:54:53.757717+00:00
-- url     : https://prove2.me/theorems/c2a36122-4e1f-4e5f-a55a-a48156cbeaf5
-- title:
--   §1–§4, pp. 892–911 — L_m distance, boxes, stickiness, cells, BBD-trees and their leaf cells, distance to a cell, the search's termination rule
-- statement:
--   This file fixes the objects of Arya, Mount, Netanyahu, Silverman and Wu's analysis of approximate nearest neighbor search in a BBD-tree. Throughout, points live in $\mathbb R^d$.
--
--   1. **Minkowski distance** (p. 892). For an integer $m\ge 1$ the $L_m$ distance is
--   $$\operatorname{dist}_m(x,y)=\Big(\sum_{i=1}^d |x_i-y_i|^m\Big)^{1/m},$$
--   and for $m=\infty$ it is $\max_i |x_i-y_i|$.
--   2. **Rectangles and boxes** (p. 897). A rectangle is a product $\prod_i [\ell_i,h_i]$ of closed intervals; its $i$th length is $h_i-\ell_i$ and its **size** is the length of its longest side. A **box** is a rectangle with positive sides whose aspect ratio (longest over shortest side) is at most $3$.
--   3. **Stickiness** (p. 897). An interval $[x_I,y_I]\subseteq[x_O,y_O]$ is sticky for $[x_O,y_O]$ if each of the gaps $x_I-x_O$ and $y_O-y_I$ is either $0$ or at least the width $w=y_I-x_I$. A box $b_I$ is sticky for $b_O$ if each of its $d$ intervals is sticky for the corresponding interval of $b_O$.
--   4. **Cells** (p. 897). A cell has an outer box $b_O$ and an optional inner box $b_I$. As a point set it is $b_O$, or the closure of $b_O\setminus b_I$ (cells are closed). Its size is the size of its outer box. A cell is well formed when its outer box is a box and its inner box, if present, is a box, sticky for $b_O$, and different from $b_O$.
--   5. **BBD-trees** (§2.1, p. 898). A tree is a leaf, a fair split of a cell by a hyperplane $x_i=t$ into a low and a high child, or a shrink by a shrinking box $b$ into an inner child (outer box $b$, keeping the parent's inner box) and an outer child (outer box the parent's, inner box $b$). A tree is **valid** for a root cell when every node's cell is well formed (aspect ratio bound and stickiness), every split plane cuts the outer box properly, and the parent's inner box lies entirely within one child of a split (and, through stickiness, inside the shrinking box of a shrink). The **leaf cells** are the cells at the leaves.
--   6. **Distance to a cell** (property (e), p. 908): $\operatorname{dist}_m(q,c)=\inf\{\operatorname{dist}_m(q,x): x\in c\}$.
--   7. **The search** (§4, p. 911). Given an enumeration $E=((c_0,p_0),(c_1,p_1),\dots)$ of leaf cells with associated data points, the search **stops at position $j$** if, after processing cell $c_j$, the distance from $q$ to $c_j$ exceeds $\operatorname{dist}_m(q,p)/(1+\varepsilon)$, where $p$ is the closest point among $p_0,\dots,p_j$. A number $N$ is the **visit count** if no position before $N$ stops the search and position $N$ does, unless $N$ equals the length of $E$.
--   8. **Approximate nearest neighbor** (p. 893). For a finite set $S$, a point $p\in S$ is a $(1+\varepsilon)$-approximate nearest neighbor of $q$ if $\operatorname{dist}_m(q,p)\le(1+\varepsilon)\operatorname{dist}_m(q,x)$ for all $x\in S$.
--
--   These objects are shared by every statement of the mission: the packing bound for leaf cells, the size bound for visited cells and the bound on the number of visited cells.
--
--   **Formalization Note** Points are `Fin d → ℝ`; $m$ ranges over `ℕ∞` with `⊤` for $\infty$, and every statement assumes $1\le m$. A rectangle is a pair of corner vectors, its point set `Set.Icc lo hi`. Positive sides in a box are needed for the aspect ratio to make sense; an inner box equal to the outer box is excluded because it would leave an empty cell. The cell's point set is the closure of the difference, not the difference with the open interior removed, which would keep isolated boundary points. The construction algorithms of §2.2–§2.5 are not formalized: the tree is any tree satisfying the §2.1 invariants. The paper's root is a hypercube; the root here may be any box.
-- source:
--   Arya et al., An optimal algorithm for approximate nearest neighbor searching in fixed dimensions, J. ACM 45 (1998), pp. 892–893 (L_m distance, (1+ε)-ANN), 897–898 (rectangles, boxes, cells, stickiness, splits, shrinks, invariants), 908 (property (e)), 911 (§4, the search)

import Mathlib

namespace AryaANN.Search

/-- The Minkowski `L_m` distance on `ℝ^d` (p. 892): the `m`th root of `∑ |x_i - y_i|^m` for finite
`m`, and `max_i |x_i - y_i|` for `m = ∞` (encoded as `⊤ : ℕ∞`). -/
noncomputable def lmDist {d : ℕ} (m : ℕ∞) (x y : Fin d → ℝ) : ℝ :=
  if m = ⊤ then ⨆ i, |x i - y i|
  else (∑ i, |x i - y i| ^ m.toNat) ^ ((1 : ℝ) / m.toNat)

/-- An axis-parallel rectangle `∏ [lo i, hi i]` (p. 897). -/
structure Rect (d : ℕ) where
  lo : Fin d → ℝ
  hi : Fin d → ℝ

/-- The point set of a rectangle: the product of the closed intervals `[lo i, hi i]`. -/
def Rect.toSet {d : ℕ} (R : Rect d) : Set (Fin d → ℝ) := Set.Icc R.lo R.hi

/-- The `i`th length of a rectangle (p. 897). -/
def Rect.len {d : ℕ} (R : Rect d) (i : Fin d) : ℝ := R.hi i - R.lo i

/-- The size of a rectangle: the length of its longest side (p. 897). -/
noncomputable def Rect.size {d : ℕ} (R : Rect d) : ℝ := ⨆ i, R.len i

/-- A box: a rectangle with positive sides whose aspect ratio (longest side over shortest side)
is at most 3 (p. 897). -/
def IsBox {d : ℕ} (R : Rect d) : Prop := ∀ i, 0 < R.len i ∧ R.size ≤ 3 * R.len i

/-- `[xI, yI] ⊆ [xO, yO]` is sticky: each of the gaps `xI - xO`, `yO - yI` is `0` or at least
the inner width `yI - xI` (p. 897). -/
def IntervalSticky (xI yI xO yO : ℝ) : Prop :=
  xO ≤ xI ∧ yI ≤ yO ∧ (xI - xO = 0 ∨ yI - xI ≤ xI - xO) ∧ (yO - yI = 0 ∨ yI - xI ≤ yO - yI)

/-- The inner box `bI` is sticky for the outer box `bO`: coordinatewise stickiness (p. 897). -/
def IsSticky {d : ℕ} (bI bO : Rect d) : Prop :=
  ∀ i, IntervalSticky (bI.lo i) (bI.hi i) (bO.lo i) (bO.hi i)

/-- A cell: an outer box and an optional inner box (p. 897). -/
structure Cell (d : ℕ) where
  outer : Rect d
  inner : Option (Rect d)

/-- The (closed) point set of a cell (p. 897): the outer box if there is no inner box, and the
closure of `outer \ inner` otherwise. -/
def Cell.toSet {d : ℕ} (c : Cell d) : Set (Fin d → ℝ) :=
  match c.inner with
  | none => c.outer.toSet
  | some b => closure (c.outer.toSet \ b.toSet)

/-- The size of a cell is the size of its outer box (p. 897). -/
noncomputable def Cell.size {d : ℕ} (c : Cell d) : ℝ := c.outer.size

/-- A well-formed cell: the outer box is a box, and the inner box, if any, is a box, sticky for
the outer box, and different from it. -/
def Cell.WF {d : ℕ} (c : Cell d) : Prop :=
  IsBox c.outer ∧ ∀ b ∈ c.inner, IsBox b ∧ IsSticky b c.outer ∧ b ≠ c.outer

/-- The shape of a BBD-tree (§2.1, p. 898): a leaf, a fair split by the hyperplane `x_i = t`
(low child, high child), or a shrink by the shrinking box `b` (inner child, outer child). -/
inductive BBDTree (d : ℕ) where
  | leaf : BBDTree d
  | split (i : Fin d) (t : ℝ) (low high : BBDTree d) : BBDTree d
  | shrink (b : Rect d) (inner outer : BBDTree d) : BBDTree d

/-- The low child of the fair split of `c` at `x_i = t`; the parent's inner box goes to it iff it
lies on the low side. -/
noncomputable def Cell.splitLow {d : ℕ} (c : Cell d) (i : Fin d) (t : ℝ) : Cell d :=
  ⟨⟨c.outer.lo, Function.update c.outer.hi i t⟩,
   match c.inner with
   | some b => if b.hi i ≤ t then some b else none
   | none => none⟩

/-- The high child of the fair split of `c` at `x_i = t`; the parent's inner box goes to it iff it
lies on the high side. -/
noncomputable def Cell.splitHigh {d : ℕ} (c : Cell d) (i : Fin d) (t : ℝ) : Cell d :=
  ⟨⟨Function.update c.outer.lo i t, c.outer.hi⟩,
   match c.inner with
   | some b => if t ≤ b.lo i then some b else none
   | none => none⟩

/-- The §2.1 invariants (p. 898) along the whole tree, relative to the cell `c` of its root: every
node's cell is well formed (aspect ratio, stickiness); a split plane cuts the outer box properly
and does not cut the inner box; the inner child of a shrink by `b` is `⟨b, inner⟩` (so the
parent's inner box lies in the shrinking box) and the outer child is `⟨outer, some b⟩`. -/
def Valid {d : ℕ} : Cell d → BBDTree d → Prop
  | c, .leaf => c.WF
  | c, .split i t low high =>
      c.WF ∧ c.outer.lo i < t ∧ t < c.outer.hi i ∧ (∀ b ∈ c.inner, b.hi i ≤ t ∨ t ≤ b.lo i) ∧
      Valid (c.splitLow i t) low ∧ Valid (c.splitHigh i t) high
  | c, .shrink b tIn tOut => c.WF ∧ Valid ⟨b, c.inner⟩ tIn ∧ Valid ⟨c.outer, some b⟩ tOut

/-- The leaf cells of a tree whose root has cell `c`, left to right. -/
noncomputable def leaves {d : ℕ} : Cell d → BBDTree d → List (Cell d)
  | c, .leaf => [c]
  | c, .split i t low high => leaves (c.splitLow i t) low ++ leaves (c.splitHigh i t) high
  | c, .shrink b tIn tOut => leaves ⟨b, c.inner⟩ tIn ++ leaves ⟨c.outer, some b⟩ tOut

/-- The distance from `q` to a cell: the closest distance between `q` and any point of the cell
(property (e), p. 908). -/
noncomputable def cellDist {d : ℕ} (m : ℕ∞) (q : Fin d → ℝ) (c : Cell d) : ℝ :=
  sInf ((lmDist m q) '' c.toSet)

/-- The search (§4, p. 911) on an enumeration `E` of (leaf cell, associated data point) stops at
position `j`: cell `j` has been processed, and its distance from `q` exceeds
`dist(q, p) / (1 + ε)` for the closest point `p` among the points of positions `0, …, j`. -/
def StopsAt {d : ℕ} (m : ℕ∞) (ε : ℝ) (q : Fin d → ℝ) (E : List (Cell d × (Fin d → ℝ)))
    (j : ℕ) : Prop :=
  ∃ hj : j < E.length, ∃ i, ∃ hi : i < E.length, i ≤ j ∧
    lmDist m q (E[i]'hi).2 / (1 + ε) < cellDist m q (E[j]'hj).1

/-- `N` is the number of leaf cells visited up until termination: no position before `N` stops
the search, and position `N` stops it unless the enumeration is exhausted. -/
def IsVisitCount {d : ℕ} (m : ℕ∞) (ε : ℝ) (q : Fin d → ℝ) (E : List (Cell d × (Fin d → ℝ)))
    (N : ℕ) : Prop :=
  N ≤ E.length ∧ (∀ j < N, ¬ StopsAt m ε q E j) ∧ (N < E.length → StopsAt m ε q E N)

/-- `p` is a `(1 + ε)`-approximate nearest neighbor of `q` in `S` (p. 893). -/
def IsApproxNN {d : ℕ} (m : ℕ∞) (ε : ℝ) (S : Finset (Fin d → ℝ)) (q p : Fin d → ℝ) : Prop :=
  p ∈ S ∧ ∀ x ∈ S, lmDist m q p ≤ (1 + ε) * lmDist m q x

end AryaANN.Search



-- Prove2me | Definitions.Def_BinPacking_Decreasing_Model
-- name    : BinPacking_Decreasing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:13:39.183889+00:00
-- url     : https://prove2.me/theorems/7db8be8c-1c85-4a2d-b52c-c8f522174c29
-- title:
--   Bin packing: lists in (0, 1], the optimum $L^*$, the First-Fit and Best-Fit runs, and First-Fit Decreasing and Best-Fit Decreasing
-- statement:
--   This file sets up the one-dimensional bin-packing model of Johnson, Demers, Ullman, Garey and Graham (1974).
--
--   A **list** is a finite sequence $L=(a_1,a_2,\dots,a_n)$ of real numbers in $(0,1]$; values may repeat. A **bin** has capacity $1$, and its **level** is the sum of the numbers placed in it. The optimum $L^*$ is the minimum number of bins into which the elements of $L$ can be placed so that no bin contains numbers whose sum exceeds $1$.
--
--   Two on-line placement rules place $a_1,a_2,\dots,a_n$ in this order into bins $B_1,B_2,\dots$, all initially at level $0$:
--
--   1. **First-Fit (FF).** Place $a_i$ into the bin $B_j$ of least index whose level $\beta$ satisfies $\beta\le 1-a_i$.
--   2. **Best-Fit (BF).** Among the bins whose level $\beta$ satisfies $\beta\le 1-a_i$, choose one of largest level, and among those the one of least index; place $a_i$ there.
--
--   **First-Fit Decreasing (FFD)** and **Best-Fit Decreasing (BFD)** first arrange $L$ into nonincreasing order and then apply FF, respectively BF, to the arranged list. $FF(L)$, $BF(L)$, $FFD(L)$ and $BFD(L)$ denote the number of bins that receive at least one element.
--
--   The history of a run is also recorded: for each element, the bin it is placed into and its position in that bin (how many elements the bin already held when it arrived). Position $(j,k)$ in the paper's notation is the $k$-th element placed into bin $B_j$.
--
--   These objects are used by every statement of the mission.
--
--   **Formalization Note** A list is `L : List ℝ` with the predicate `IsList L` ($0<a\le 1$ for every element), and every statement assumes it. $L^*$ is `optBins L`, the least `b : ℕ` for which some map `Fin L.length → Fin b` has every bin sum at most $1$ (an `sInf` on `ℕ`, which would be $0$ on an empty set; `IsList` makes the set nonempty; the empty list has $L^*=0$). A run keeps only the nonempty bins, as a `List (List ℝ)` in index order, each bin holding its contents in placement order; a new bin is opened at the end exactly when no nonempty bin fits. This is the paper's "least $j$" over infinitely many initially empty bins: for FF the empty bins all come after the nonempty ones, and for BF every element is positive, so any nonempty bin that fits has a larger level than an empty one. The fit test is the non-strict $\beta+a_i\le 1$, and comparisons of reals use classical decidability (the definitions are noncomputable). The arrangement into nonincreasing order is `sortDesc`, a stable merge sort with comparison $b\le a$; equal elements keep their order from $L$, and since equal elements are interchangeable the bin counts do not depend on this choice. Indices are $0$-based: item `i` is the paper's $a_{i+1}$ and bin `j` is $B_{j+1}$; `binOf choose L i` and `slotOf choose L i` read the bin and the in-bin position (both $0$-based) off the run on the first `i` items.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), pp. 300-301, Section 1 (the problem, Algorithms 1-4, FF(L), BF(L), FFD(L), BFD(L)); p. 310, proof of Theorem 3.4 (positions (j, k))

import Mathlib

namespace BinPacking.Decreasing

/-- The standing hypothesis of the paper (p. 300): `L = (a₁, …, aₙ)` is a list of real numbers
in `(0, 1]`. Lists are read left to right and may repeat values. -/
def IsList (L : List ℝ) : Prop := ∀ a ∈ L, 0 < a ∧ a ≤ 1

/-- `L*` (p. 300): the minimum number `b` of unit bins such that the items of `L` can be assigned
to bins `0, …, b - 1` (a map `Fin L.length → Fin b`) with every bin sum at most `1`.
`sInf` on `ℕ` is `0` on the empty set; for a list satisfying `IsList` the set is nonempty
(`b = L.length` works), so `IsList` is assumed wherever `optBins` is used. `optBins [] = 0`. -/
noncomputable def optBins (L : List ℝ) : ℕ :=
  sInf {b : ℕ | ∃ f : Fin L.length → Fin b, ∀ j : Fin b,
    ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i ≤ 1}

/-- Place item `a` into bin number `j` (0-based) of the current list of nonempty bins; if `j` is
not the index of an existing bin, open a new bin `[a]` at the end. Each bin records its contents
in placement order. -/
def placeAt (bins : List (List ℝ)) (j : ℕ) (a : ℝ) : List (List ℝ) :=
  if j < bins.length then bins.mapIdx (fun i B => if i = j then B ++ [a] else B)
  else bins ++ [[a]]

/-- First-fit choice (Algorithm 1, p. 300): the least index of a nonempty bin whose level
`β` satisfies `β ≤ 1 - a`, i.e. `β + a ≤ 1`; `bins.length` (a new bin) if there is none. -/
noncomputable def ffChoice (bins : List (List ℝ)) (a : ℝ) : ℕ :=
  bins.findIdx (fun B => decide (B.sum + a ≤ 1))

/-- Best-fit choice (Algorithm 2, p. 300): the least index of a nonempty bin whose level `β`
satisfies `β + a ≤ 1` and is as large as possible among such bins; `bins.length` (a new bin) if
no nonempty bin fits. -/
noncomputable def bfChoice (bins : List (List ℝ)) (a : ℝ) : ℕ :=
  bins.findIdx (fun B => decide (B.sum + a ≤ 1 ∧ ∀ B' ∈ bins, B'.sum + a ≤ 1 → B'.sum ≤ B.sum))

/-- The run of an on-line placement rule `choose` on `L`: the items are placed in list order,
starting from no bins. The result is the list of nonempty bins `B₁, B₂, …` in index order. -/
noncomputable def run (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ) : List (List ℝ) :=
  L.foldl (fun bins a => placeAt bins (choose bins a) a) []

/-- `FF(L)` (p. 301): the number of bins used by first-fit (Algorithm 1) on `L`. -/
noncomputable def FF (L : List ℝ) : ℕ := (run ffChoice L).length

/-- `BF(L)` (p. 301): the number of bins used by best-fit (Algorithm 2) on `L`. -/
noncomputable def BF (L : List ℝ) : ℕ := (run bfChoice L).length

/-- `L` arranged into nonincreasing order (Algorithms 3 and 4, p. 300), by a stable merge sort
with the comparison `b ≤ a`: equal items keep their relative order from `L`. -/
noncomputable def sortDesc (L : List ℝ) : List ℝ :=
  L.mergeSort (fun a b => decide (b ≤ a))

/-- `FFD(L)` (Algorithm 3, p. 300; notation p. 301): the number of bins used by first-fit
applied to `L` arranged into nonincreasing order. -/
noncomputable def FFD (L : List ℝ) : ℕ := FF (sortDesc L)

/-- `BFD(L)` (Algorithm 4, p. 300; notation p. 301): the number of bins used by best-fit
applied to `L` arranged into nonincreasing order. -/
noncomputable def BFD (L : List ℝ) : ℕ := BF (sortDesc L)

/-- History of a run: the (0-based) index of the bin into which item number `i` (0-based, the
paper's `a_{i+1}`) is placed. It is the rule's choice on the bins produced by the first `i`
items; it equals the number of bins so far when the item opens a new bin. -/
noncomputable def binOf (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ) (i : Fin L.length) : ℕ :=
  choose (run choose (L.take i)) (L.get i)

/-- History of a run: the (0-based) position that item number `i` fills inside its bin, i.e.
the number of items already in that bin just before item `i` is placed (`0` when it opens a new
bin). The paper's position `(j, k)` (p. 310) is `(binOf + 1, slotOf + 1)`. -/
noncomputable def slotOf (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ) (i : Fin L.length) : ℕ :=
  ((run choose (L.take i)).getD (binOf choose L i) []).length

end BinPacking.Decreasing



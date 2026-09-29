-- Prove2me | Definitions.Def_BinPacking_SmallItems_Model
-- name    : BinPacking_SmallItems_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:18:57.170061+00:00
-- url     : https://prove2.me/theorems/be76f7db-e00e-4fc6-832c-e98c9218d956
-- title:
--   Bin packing: lists in (0, 1], the optimum $L^*$, the First-Fit run, and First-Fit Decreasing $FFD(L)$
-- statement:
--   This file sets up the one-dimensional bin-packing model of Johnson, Demers, Ullman, Garey and Graham (1974) as far as First-Fit Decreasing.
--
--   A **list** is a finite sequence $L=(a_1,a_2,\dots,a_n)$ of real numbers in $(0,1]$; values may repeat. A **bin** has capacity $1$, and its **level** is the sum of the numbers placed in it. The optimum $L^*$ is the minimum number of bins into which the elements of $L$ can be placed so that no bin contains numbers whose sum exceeds $1$.
--
--   **First-Fit (FF)** places $a_1,a_2,\dots,a_n$ in this order into bins $B_1,B_2,\dots$, all initially at level $0$: the element $a_i$ goes into the bin $B_j$ of least index whose level $\beta$ satisfies $\beta\le 1-a_i$. $FF(L)$ is the number of bins that receive at least one element. The run also records, for each element, the bin it was placed into.
--
--   **First-Fit Decreasing (FFD)** arranges $L$ into nonincreasing order and applies First-Fit to the derived list; $FFD(L)$ is the number of bins it uses.
--
--   These objects are used by every statement of the mission.
--
--   **Formalization Note** A list is `L : List ℝ` with the predicate `IsList L` ($0<a\le 1$ for every element), and every statement assumes it. $L^*$ is `optBins L`, the least `b : ℕ` for which some map `Fin L.length → Fin b` has every bin sum at most $1$ (an `sInf` on `ℕ`, which would be $0$ on an empty set; `IsList` makes the set nonempty; $L^*$ of the empty list is $0$). The run keeps only the nonempty bins, as a `List (List ℝ)` in index order, each bin holding its contents in placement order; a new bin is opened at the end exactly when no nonempty bin fits, which is the paper's "least $j$" because all empty bins come after the nonempty ones. The fit test is the non-strict $\beta+a_i\le 1$, and comparisons of reals use classical decidability (the definitions are noncomputable). Indices are $0$-based: item `i` is the paper's $a_{i+1}$ and bin `j` is $B_{j+1}$; `ffBinOf L i` is the bin chosen for item `i` by the run on the first `i` items, which is also its bin in the final packing because bins are never reordered. The nonincreasing rearrangement `sortDesc L` is `List.mergeSort` with the comparison $b\le a$; equal elements are interchangeable, so the order among ties does not affect $FFD(L)$.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), pp. 300-301, Section 1 (the problem, Algorithms 1 and 3, FFD(L))

import Mathlib

namespace BinPacking.SmallItems

/-- The standing hypothesis of the paper (p. 300): `L = (a₁, …, aₙ)` is a list of real numbers
in `(0, 1]`. Lists are read left to right and may repeat values. -/
def IsList (L : List ℝ) : Prop := ∀ a ∈ L, 0 < a ∧ a ≤ 1

/-- `L*` (p. 300): the minimum number `b` of unit bins such that the items of `L` can be assigned
to bins `0, …, b - 1` (a map `Fin L.length → Fin b`) with every bin sum at most `1`.
`sInf` on `ℕ` is `0` on the empty set; for a list satisfying `IsList` the set is nonempty
(`b = L.length` works), so `IsList` is assumed wherever `optBins` is used. -/
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

/-- The first-fit run on `L`: the items are placed in list order, starting from no bins.
The result is the list of nonempty bins `B₁, B₂, …` in index order. -/
noncomputable def ffPack (L : List ℝ) : List (List ℝ) :=
  L.foldl (fun bins a => placeAt bins (ffChoice bins a) a) []

/-- `FF(L)` (p. 301): the number of bins used by first-fit on `L`. -/
noncomputable def FF (L : List ℝ) : ℕ := (ffPack L).length

/-- History of the first-fit run: the (0-based) index of the bin into which item number `i`
(0-based, the paper's `a_{i+1}`) is placed. It is first-fit's choice on the bins produced by the
first `i` items. Bins are never reordered, so it is also the item's bin in the final packing. -/
noncomputable def ffBinOf (L : List ℝ) (i : Fin L.length) : ℕ :=
  ffChoice (ffPack (L.take i)) (L.get i)

/-- The list `L` arranged into nonincreasing order (the first step of Algorithm 3, p. 300). -/
noncomputable def sortDesc (L : List ℝ) : List ℝ :=
  L.mergeSort (fun a b => decide (b ≤ a))

/-- The first-fit decreasing packing of `L` (Algorithm 3, p. 300): first-fit applied to the
nonincreasing rearrangement of `L`. -/
noncomputable def ffdPack (L : List ℝ) : List (List ℝ) := ffPack (sortDesc L)

/-- `FFD(L)` (p. 301): the number of bins used by first-fit decreasing on `L`. -/
noncomputable def FFD (L : List ℝ) : ℕ := FF (sortDesc L)

end BinPacking.SmallItems



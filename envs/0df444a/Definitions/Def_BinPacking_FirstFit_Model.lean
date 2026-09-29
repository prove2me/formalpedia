-- Prove2me | Definitions.Def_BinPacking_FirstFit_Model
-- name    : BinPacking_FirstFit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:04:39.349889+00:00
-- url     : https://prove2.me/theorems/295ceaba-9d11-44a6-ae3a-8c4b9b4d8cf2
-- title:
--   Bin packing: lists in (0, 1], the optimum $L^*$, the First-Fit and Best-Fit runs, coarseness, and the ratios $R_{FF}(k)$, $R_{BF}(k)$
-- statement:
--   This file sets up the one-dimensional bin-packing model of Johnson, Demers, Ullman, Garey and Graham (1974).
--
--   A **list** is a finite sequence $L=(a_1,a_2,\dots,a_n)$ of real numbers in $(0,1]$; values may repeat. A **bin** has capacity $1$, and its **level** is the sum of the numbers placed in it. The optimum $L^*$ is the minimum number of bins into which the elements of $L$ can be placed so that no bin contains numbers whose sum exceeds $1$.
--
--   The two on-line placement rules place $a_1,a_2,\dots,a_n$ in this order into bins $B_1,B_2,\dots$, all initially at level $0$:
--
--   1. **First-Fit (FF).** Place $a_i$ into the bin $B_j$ of least index whose level $\beta$ satisfies $\beta\le 1-a_i$.
--   2. **Best-Fit (BF).** Among the bins whose level $\beta$ satisfies $\beta\le 1-a_i$, choose one of largest level, and among those the one of least index; place $a_i$ there.
--
--   $FF(L)$ and $BF(L)$ denote the number of bins that receive at least one element. The history of a run is also recorded: for each element $a_i$, the bin it is placed into and that bin's level just before $a_i$ arrives.
--
--   The **coarseness** of a bin $B_j$ of a completed packing is the largest $\alpha$ such that some bin of smaller index is filled to level $1-\alpha$, i.e.
--   $$\operatorname{coarseness}(B_j)=\max_{j'<j}\bigl(1-\operatorname{level}(B_{j'})\bigr),$$
--   and the coarseness of the first bin is $0$.
--
--   Finally, for $k\ge 1$,
--   $$R_{FF}(k)=\sup\Bigl\{\tfrac{FF(L)}{L^*} : L^*=k\Bigr\},\qquad R_{BF}(k)=\sup\Bigl\{\tfrac{BF(L)}{L^*} : L^*=k\Bigr\},$$
--   the worst-case ratio of the algorithm over all lists whose optimum is $k$.
--
--   These objects are used by every statement of the mission.
--
--   **Formalization Note** A list is `L : List ℝ` with the predicate `IsList L` ($0<a\le 1$ for every element), and every statement assumes it. $L^*$ is `optBins L`, the least `b : ℕ` for which some map `Fin L.length → Fin b` has every bin sum at most $1$ (an `sInf` on `ℕ`, which would be $0$ on an empty set; `IsList` makes the set nonempty). A run keeps only the nonempty bins, as a `List (List ℝ)` in index order, each bin holding its contents in placement order; a new bin is opened at the end exactly when no nonempty bin fits. This is the paper's "least $j$" over infinitely many initially empty bins: for FF the empty bins all come after the nonempty ones, and for BF every element is positive, so any nonempty bin that fits has a larger level than an empty one. The fit test is the non-strict $\beta+a_i\le 1$, and comparisons of reals use classical decidability (the definitions are noncomputable). Indices are $0$-based: item `i` is the paper's $a_{i+1}$ and bin `j` is $B_{j+1}$; `binOf choose L i` and `levelBefore choose L i` read the history off the run on the first `i` items. Coarseness is computed in the completed packing as the maximum of $0$ and the values $1-\text{level}$ over earlier bins (all levels are at most $1$, so the extra $0$ changes nothing). $R_{FF}$ and $R_{BF}$ are suprema in the extended nonnegative reals $[0,\infty]$, so that an empty or unbounded family is not silently $0$; the paper's "maximum" is this supremum. At $k=0$ the only list is the empty one and the value is $0/0=0$.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), pp. 300-301, Section 1 (the problem, Algorithms 1 and 2, FF(L), BF(L), R_FF(k), R_BF(k)); p. 305, Section 2 (coarseness)

import Mathlib

namespace BinPacking.FirstFit

open scoped ENNReal

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

/-- Best-fit choice (Algorithm 2, p. 300): the least index of a nonempty bin whose level `β`
satisfies `β + a ≤ 1` and is as large as possible among such bins; `bins.length` (a new bin) if
no nonempty bin fits. -/
noncomputable def bfChoice (bins : List (List ℝ)) (a : ℝ) : ℕ :=
  bins.findIdx (fun B => decide (B.sum + a ≤ 1 ∧ ∀ B' ∈ bins, B'.sum + a ≤ 1 → B'.sum ≤ B.sum))

/-- The run of an on-line placement rule `choose` on `L`: the items are placed in list order,
starting from no bins. The result is the list of nonempty bins `B₁, B₂, …` in index order. -/
noncomputable def run (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ) : List (List ℝ) :=
  L.foldl (fun bins a => placeAt bins (choose bins a) a) []

/-- The completed first-fit packing of `L`. -/
noncomputable def ffPack (L : List ℝ) : List (List ℝ) := run ffChoice L

/-- The completed best-fit packing of `L`. -/
noncomputable def bfPack (L : List ℝ) : List (List ℝ) := run bfChoice L

/-- `FF(L)` (p. 301): the number of bins used by first-fit on `L`. -/
noncomputable def FF (L : List ℝ) : ℕ := (ffPack L).length

/-- `BF(L)` (p. 301): the number of bins used by best-fit on `L`. -/
noncomputable def BF (L : List ℝ) : ℕ := (bfPack L).length

/-- History of a run: the (0-based) index of the bin into which item number `i` (0-based, the
paper's `a_{i+1}`) is placed. It is the rule's choice on the bins produced by the first `i` items. -/
noncomputable def binOf (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ) (i : Fin L.length) : ℕ :=
  choose (run choose (L.take i)) (L.get i)

/-- History of a run: the level of the bin receiving item number `i`, just before that item is
placed (`0` when the item opens a new bin). -/
noncomputable def levelBefore (choose : List (List ℝ) → ℝ → ℕ) (L : List ℝ)
    (i : Fin L.length) : ℝ :=
  ((run choose (L.take i)).getD (binOf choose L i) []).sum

/-- Coarseness (p. 305) of bin number `j` (0-based) of a completed packing `P`: the largest `α`
such that some bin with smaller index is filled to level `1 - α`, i.e.
`max_{j' < j} (1 - level of bin j')`; the coarseness of the first bin is `0`. (The maximum is
taken together with `0`; in every packing produced by FF or BF all levels are at most `1`, so
this changes nothing.) -/
def coarseness (P : List (List ℝ)) (j : ℕ) : ℝ :=
  ((P.take j).map (fun B => 1 - B.sum)).foldr max 0

/-- `R_FF(k)` (p. 301): the supremum of `FF(L)/L*` over all lists `L` (of reals in `(0, 1]`) with
`L* = k`, computed in `ℝ≥0∞` so that an empty or unbounded family is not silently `0`.
At `k = 0` the only such list is the empty one, and the value is `0/0 = 0`. -/
noncomputable def ratioFF (k : ℕ) : ℝ≥0∞ :=
  ⨆ (L : List ℝ) (_ : IsList L) (_ : optBins L = k), (FF L : ℝ≥0∞) / (k : ℝ≥0∞)

/-- `R_BF(k)` (p. 301): the supremum of `BF(L)/L*` over all lists `L` with `L* = k`, in `ℝ≥0∞`. -/
noncomputable def ratioBF (k : ℕ) : ℝ≥0∞ :=
  ⨆ (L : List ℝ) (_ : IsList L) (_ : optBins L = k), (BF L : ℝ≥0∞) / (k : ℝ≥0∞)

end BinPacking.FirstFit



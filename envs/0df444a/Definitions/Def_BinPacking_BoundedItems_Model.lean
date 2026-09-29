-- Prove2me | Definitions.Def_BinPacking_BoundedItems_Model
-- name    : BinPacking_BoundedItems_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:09:45.906173+00:00
-- url     : https://prove2.me/theorems/3951d488-2ab9-4890-95b5-0c14dab06c0f
-- title:
--   Bin packing: lists in (0, 1], the optimum L*, the First-Fit and Best-Fit runs, and the restricted ratios $R^\alpha_{FF}(k)$, $R^\alpha_{BF}(k)$
-- statement:
--   This file sets up the one-dimensional bin-packing model of Johnson, Demers, Ullman, Garey and Graham (1974).
--
--   A **list** is a finite sequence $L=(a_1,a_2,\dots,a_n)$ of real numbers in $(0,1]$; values may repeat. The **optimum** $L^*$ is the minimum number of unit-capacity bins into which the elements of $L$ can be placed so that no bin contains numbers whose sum exceeds $1$. The **level** of a bin is the sum of its contents.
--
--   **First-Fit** (Algorithm 1) places $a_1,a_2,\dots,a_n$ in that order; to place $a_i$ it finds the least $j$ such that bin $B_j$ is filled to a level $\beta\le 1-a_i$ and puts $a_i$ there. **Best-Fit** (Algorithm 2) does the same, except that among the bins with level $\beta\le 1-a_i$ it takes one whose level $\beta$ is as large as possible, and the least index among those. $FF(L)$ and $BF(L)$ denote the numbers of bins used.
--
--   For $0<\alpha$ and an integer $k\ge 0$, the **restricted worst-case ratios** are
--   $$R^\alpha_{FF}(k)=\sup\Big\{\tfrac{FF(L)}{k} : L\subseteq(0,\alpha],\ L^*=k\Big\},\qquad R^\alpha_{BF}(k)=\sup\Big\{\tfrac{BF(L)}{k} : L\subseteq(0,\alpha],\ L^*=k\Big\}.$$
--
--   These objects are used by every statement of the mission.
--
--   **Formalization Note** A list is `L : List ℝ`, 0-based, with the standing hypothesis `IsList L` ($0<a\le 1$ for every element). $L^*$ is `optBins L`, the `sInf` in `ℕ` of the numbers $b$ admitting an assignment `Fin L.length → Fin b` with every bin sum $\le 1$; for a list satisfying `IsList` this set is nonempty, while `sInf ∅ = 0`, so `IsList` accompanies every use. A run keeps the list of *nonempty* bins in the order they were opened, each with its contents in placement order; an item that fits in no open bin opens a new bin at the end. This is the paper's "least $j$" over infinitely many initially empty bins: for First-Fit the empty bins all come after the nonempty ones, and for Best-Fit a nonempty bin has positive level, larger than an empty bin's level $0$. Real numbers are compared exactly (classical decidability), so the definitions are noncomputable. The ratios are suprema in $[0,\infty]$ (`ℝ≥0∞`), so an unbounded family is $+\infty$ rather than a junk value; at $k=0$ the only admissible list is empty and the value is $0$.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), pp. 300-301, Section 1 (problem, Algorithms 1 and 2, R_FF(k), R_BF(k)); p. 308, R^α_FF(k), R^α_BF(k)

import Mathlib

namespace BinPacking.BoundedItems

open scoped ENNReal

/-- The standing hypothesis of Johnson–Demers–Ullman–Garey–Graham (1974), p. 300: a list
`L = (a₁, a₂, …, a_n)` of real numbers in `(0, 1]`. Lists are read left to right and may
repeat values. -/
def IsList (L : List ℝ) : Prop :=
  ∀ a ∈ L, 0 < a ∧ a ≤ 1

/-- `f` places the items of `L` (indexed `0, …, n − 1`) into `b` bins so that no bin contains
numbers whose sum exceeds `1`. -/
def IsPacking (L : List ℝ) (b : ℕ) (f : Fin L.length → Fin b) : Prop :=
  ∀ j : Fin b, ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i ≤ 1

/-- `L*` (p. 300): the minimum number of bins into which the elements of `L` can be placed so
that no bin contains numbers whose sum exceeds `1`. For a list satisfying `IsList` the set is
nonempty (`b = n`, one item per bin); `sInf ∅ = 0` on `ℕ`, so `IsList` must accompany every use.
`optBins [] = 0`. -/
noncomputable def optBins (L : List ℝ) : ℕ :=
  sInf {b : ℕ | ∃ f : Fin L.length → Fin b, IsPacking L b f}

/-- The level of a bin: the sum of its contents. -/
def level (B : List ℝ) : ℝ :=
  B.sum

/-- One First-Fit placement (Algorithm 1, p. 300). The argument is the list of nonempty bins
`B₁, B₂, …` opened so far, each holding its contents in placement order. The item `a` goes into
the first bin whose level `β` satisfies `β ≤ 1 − a` (i.e. `β + a ≤ 1`); if there is none, a new
bin `[a]` is opened after the existing ones. -/
noncomputable def ffInsert (a : ℝ) : List (List ℝ) → List (List ℝ)
  | [] => [[a]]
  | B :: Bs => if level B + a ≤ 1 then (B ++ [a]) :: Bs else B :: ffInsert a Bs

/-- The First-Fit packing of `L`: the items `a₁, a₂, …, a_n` are placed in that order. -/
noncomputable def ffPack (L : List ℝ) : List (List ℝ) :=
  L.foldl (fun P a => ffInsert a P) []

/-- `FF(L)` (p. 301): the number of bins used by First-Fit on `L`. -/
noncomputable def FF (L : List ℝ) : ℕ :=
  (ffPack L).length

/-- The Best-Fit choice (Algorithm 2, p. 300) for item `a` among the open bins `P`: the least
index `i` such that bin `i` has level `β ≤ 1 − a` and `β` is as large as possible among the bins
with that property; `none` if no open bin has room. -/
noncomputable def bfChoice (a : ℝ) (P : List (List ℝ)) : Option ℕ :=
  let fits := (List.range P.length).filter (fun i => decide (level (P.getD i []) + a ≤ 1))
  fits.find? (fun i => fits.all (fun j => decide (level (P.getD j []) ≤ level (P.getD i []))))

/-- One Best-Fit placement: put `a` into the bin chosen by `bfChoice`, or open a new bin `[a]`
after the existing ones if no open bin has room. -/
noncomputable def bfInsert (a : ℝ) (P : List (List ℝ)) : List (List ℝ) :=
  match bfChoice a P with
  | some i => P.set i (P.getD i [] ++ [a])
  | none => P ++ [[a]]

/-- The Best-Fit packing of `L`: the items `a₁, a₂, …, a_n` are placed in that order. -/
noncomputable def bfPack (L : List ℝ) : List (List ℝ) :=
  L.foldl (fun P a => bfInsert a P) []

/-- `BF(L)` (p. 301): the number of bins used by Best-Fit on `L`. -/
noncomputable def BF (L : List ℝ) : ℕ :=
  (bfPack L).length

/-- `R^α_FF(k)` (p. 308): the supremum of `FF(L)/L*` over all lists `L ⊆ (0, α]` with `L* = k`,
taken in `ℝ≥0∞` (an empty family gives `0`, an unbounded one `⊤`). At `k = 0` the only such list
is the empty list, with `FF = 0`, so the value is `0`. -/
noncomputable def ratioFF (α : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ⨆ (L : List ℝ) (_ : IsList L) (_ : ∀ a ∈ L, a ≤ α) (_ : optBins L = k),
    (FF L : ℝ≥0∞) / (k : ℝ≥0∞)

/-- `R^α_BF(k)` (p. 308): the supremum of `BF(L)/L*` over all lists `L ⊆ (0, α]` with `L* = k`,
taken in `ℝ≥0∞`. -/
noncomputable def ratioBF (α : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ⨆ (L : List ℝ) (_ : IsList L) (_ : ∀ a ∈ L, a ≤ α) (_ : optBins L = k),
    (BF L : ℝ≥0∞) / (k : ℝ≥0∞)

end BinPacking.BoundedItems



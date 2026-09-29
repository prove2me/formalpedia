-- Prove2me | Definitions.Def_PLCMarkets_Rationality_EquilibriumNetwork
-- name    : PLCMarkets_Rationality_EquilibriumNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:58:21.988415+00:00
-- url     : https://prove2.me/theorems/935ca270-041c-4abc-9b5f-ef4eeea099ef
-- title:
--   Bang per buck, forced and flexible segments, and the network N(p) (§3)
-- statement:
--   Fix a Fisher market (see `FisherMarket`) and positive prices $p$. The **segments** of buyer $i$ are the segments of all her functions $f^i_j$, the last, unbounded one of each $f^i_j$ included; a segment of $f^i_j$ is a segment *of good* $j$.
--
--   1. The **bang per buck** of a segment $s$ of good $j$ is $\mathrm{bpb}(s)=\mathrm{slope}(s)/p_j$, and its **value** is $\mathrm{value}(s)=\mathrm{amount}(s)\cdot p_j$, which is infinite for an unbounded segment.
--   2. Sort buyer $i$'s segments by decreasing bang per buck into classes $Q_1,Q_2,\dots$ of equal bang per buck. Since unbounded segments have infinite value, the index $k_i$ exists (for $g\ge1$) and is the unique index with
--   $$\sum_{l<k_i}\mathrm{value}(Q_l)\le e(i)<\sum_{l\le k_i}\mathrm{value}(Q_l).$$
--   Equivalently, the bang per buck $\beta_i$ of $Q_{k_i}$ is the largest bang-per-buck value $r$ of $i$'s segments such that the segments with bang per buck $\ge r$ have total value $>e(i)$. Segments with $\mathrm{bpb}>\beta_i$ are **forced**, those with $\mathrm{bpb}=\beta_i$ are **flexible**, the rest **undesirable**.
--   3. $\mathrm{spent}(i)=\sum_{s\text{ forced}}\mathrm{value}(s)$, $\mathrm{unspent}(i)=e(i)-\mathrm{spent}(i)$; $\mathrm{forced}(j)$ is the total amount of good $j$ in all buyers' forced segments and $\mathrm{unsold}(j)=1-\mathrm{forced}(j)$.
--   4. The **network** $N(p)$ has vertices $\{s\}\cup G\cup B\cup\{t\}$, edges $(s,j)$ of capacity $\mathrm{unsold}(j)\,p_j$, edges $(i,t)$ of capacity $\mathrm{unspent}(i)$, and an edge $(j,i)$ for each flexible segment of good $j$ of buyer $i$, of capacity $\mathrm{amount}\cdot p_j$ (infinite for an unbounded segment). Its **max-flow** value is the largest value of a feasible $s$–$t$ flow.
--
--   These are the objects of Lemma 3.1 (testing whether given prices are equilibrium prices) and of the linear program of Section 4.
--
--   **Formalization Note.** The classes $Q_l$ are not indexed; $\beta_i$ is defined as the maximum (`sSup` of a finite set) described in item 2. For positive prices and $g\ge1$ that set is nonempty, since it contains the largest bang per buck of an unbounded segment; the theorems using these objects assume $p>0$, and for $g=0$ their hypotheses force $n=0$. An infinite value or capacity is encoded logically: a class containing an unbounded segment always has value exceeding $e(i)$, and an edge $(j,i)$ whose unbounded segment is flexible carries no upper bound. Parallel edges $(j,i)$ are merged into one edge whose capacity is the sum of theirs, which does not change the max-flow value. A flow is recorded by its values $y_{ji}$ on the edges $(j,i)$; the flows on $(s,j)$ and $(i,t)$ are then $\sum_iy_{ji}$ and $\sum_jy_{ji}$ by conservation. The max-flow is the `sSup` of the flow values, a maximum when $\mathrm{unsold}\ge0$ and $\mathrm{unspent}\ge0$. All objects are meaningful for positive prices; the theorems using them assume $p>0$, as the paper does ("Given nonzero prices", §3.1).
-- source:
--   Vazirani and Yannakakis, Market Equilibrium under Separable, Piecewise-Linear, Concave Utilities, J. ACM 58(3), Article 10, 2011, https://doi.org/10.1145/1970392.1970394, pp. 10:7-10:8, §3.1 (bang per buck, classes Q_l, k_i, forced/flexible/undesirable, spent, unspent, forced, unsold) and §3.2 (network N(p))

import Mathlib
import Definitions.Def_PLCMarkets_Rationality_FisherMarket

namespace PLCMarkets.Rationality

namespace FisherMarket

variable {n g : ℕ}

/-! Section 3 of Vazirani–Yannakakis 2011 (pp. 10:7–10:8): bang per buck, forced / flexible /
undesirable segments at prices `p`, and the network `N(p)`. Every `f^i_j` has its bounded
segments and one last, unbounded segment (§6, p. 10:10). All objects below are meant for
positive prices `p` (§3.1, "Given nonzero prices"). -/

/-- The bounded segments of buyer `i`: a pair `⟨j, k⟩` is the `k`-th bounded segment of `f^i_j`,
so `good(⟨j, k⟩) = j`. Together with the last, unbounded piece of every `f^i_j` (below, `tail`)
they make up `segments(i)`. -/
abbrev Seg (M : FisherMarket n g) (i : Fin n) : Type :=
  Σ j : Fin g, Fin (M.util i j).segs.length

/-- All segments of buyer `i`, `segments(i)`: `⟨j, some k⟩` is the `k`-th bounded segment of
`f^i_j` and `⟨j, none⟩` is its last, unbounded segment (of infinite amount). -/
abbrev Piece (M : FisherMarket n g) (i : Fin n) : Type :=
  Σ j : Fin g, Option (Fin (M.util i j).segs.length)

/-- `slope(s)` of a bounded segment. -/
def segSlope (M : FisherMarket n g) {i : Fin n} (s : M.Seg i) : ℚ :=
  ((M.util i s.1).segs.get s.2).1

/-- `amount(s)` of a bounded segment. -/
def segAmount (M : FisherMarket n g) {i : Fin n} (s : M.Seg i) : ℚ :=
  ((M.util i s.1).segs.get s.2).2

/-- `slope(s)` of any segment: the tail slope for the unbounded segment. -/
def pieceSlope (M : FisherMarket n g) {i : Fin n} (s : M.Piece i) : ℚ :=
  match s.2 with
  | none => (M.util i s.1).tail
  | some k => ((M.util i s.1).segs.get k).1

/-- Bang per buck `bpb(s) = slope(s) / p_j` of a bounded segment `s` of good `j`. -/
noncomputable def segBpb (M : FisherMarket n g) (p : Fin g → ℝ) {i : Fin n} (s : M.Seg i) : ℝ :=
  (M.segSlope s : ℝ) / p s.1

/-- Bang per buck `bpb(s) = slope(s) / p_j` of any segment `s` of good `j`. -/
noncomputable def pieceBpb (M : FisherMarket n g) (p : Fin g → ℝ) {i : Fin n} (s : M.Piece i) : ℝ :=
  (M.pieceSlope s : ℝ) / p s.1

/-- `value(s) = amount(s) · p_j` of a bounded segment `s` of good `j` (the unbounded segment of a
good with a positive price has infinite value). -/
noncomputable def segValue (M : FisherMarket n g) (p : Fin g → ℝ) {i : Fin n} (s : M.Seg i) : ℝ :=
  (M.segAmount s : ℝ) * p s.1

open Classical in
/-- The segments of buyer `i` with bang per buck at least `r` have total value exceeding `e(i)`:
either one of them is an unbounded segment (infinite value, positive prices), or the bounded
ones have total value exceeding `e(i)`. -/
def ValueAboveExceeds (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) (r : ℝ) : Prop :=
  (∃ j : Fin g, r ≤ M.pieceBpb p (⟨j, none⟩ : M.Piece i)) ∨
    (M.budget i : ℝ) < ∑ s ∈ Finset.univ.filter (fun s : M.Seg i => r ≤ M.segBpb p s),
      M.segValue p s

/-- The bang per buck of buyer `i`'s flexible partition `Q_{k_i}` (§3.1, "Find k_i ≥ 1 such that
Σ_{l<k_i} value(Q_l) ≤ e(i) < Σ_{l≤k_i} value(Q_l)"): the largest bang-per-buck value `r` of `i`'s
segments such that the segments with bang per buck `≥ r` (the classes `Q_1, …, Q_{k_i}`) have
total value exceeding `e(i)`. This is the maximum of a finite set, which for positive prices and
`g ≥ 1` is nonempty (it contains the largest bang per buck of an unbounded segment). -/
noncomputable def flexBpb (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) : ℝ :=
  sSup {r | r ∈ Set.range (fun s : M.Piece i => M.pieceBpb p s) ∧ M.ValueAboveExceeds p i r}

/-- A forced segment of buyer `i` at prices `p` (in `Q_1, …, Q_{k_i − 1}`); an unbounded segment
is never forced. -/
def IsForcedSeg (M : FisherMarket n g) (p : Fin g → ℝ) {i : Fin n} (s : M.Seg i) : Prop :=
  M.flexBpb p i < M.segBpb p s

/-- A flexible bounded segment of buyer `i` at prices `p` (in `Q_{k_i}`). -/
def IsFlexibleSeg (M : FisherMarket n g) (p : Fin g → ℝ) {i : Fin n} (s : M.Seg i) : Prop :=
  M.segBpb p s = M.flexBpb p i

/-- The unbounded segment of `f^i_j` is flexible for buyer `i` at prices `p` (in `Q_{k_i}`). -/
def IsFlexibleTail (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) (j : Fin g) : Prop :=
  M.pieceBpb p (⟨j, none⟩ : M.Piece i) = M.flexBpb p i

open Classical in
/-- `spent(i)`: the money buyer `i` spends on her forced segments at prices `p`. -/
noncomputable def spent (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s : M.Seg i => M.IsForcedSeg p s), M.segValue p s

/-- `unspent(i) = e(i) − spent(i)`. -/
noncomputable def unspent (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) : ℝ :=
  (M.budget i : ℝ) - M.spent p i

open Classical in
/-- The amount of good `j` in buyer `i`'s forced segments at prices `p`. -/
noncomputable def forcedAmount (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) (j : Fin g) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin (M.util i j).segs.length =>
      M.IsForcedSeg p (⟨j, k⟩ : M.Seg i)),
    (M.segAmount (⟨j, k⟩ : M.Seg i) : ℝ)

/-- `forced(j)`: the amount of good `j` sold to all buyers under their forced allocations. -/
noncomputable def forced (M : FisherMarket n g) (p : Fin g → ℝ) (j : Fin g) : ℝ :=
  ∑ i, M.forcedAmount p i j

/-- `unsold(j) = 1 − forced(j)`. -/
noncomputable def unsold (M : FisherMarket n g) (p : Fin g → ℝ) (j : Fin g) : ℝ :=
  1 - M.forced p j

open Classical in
/-- The capacity of the edge `(j, i)` of `N(p)`, parallel edges merged: the sum of
`amount(s) · p_j` over buyer `i`'s flexible bounded segments `s` of good `j` (zero, i.e. no edge,
when there is none). When the unbounded segment of `f^i_j` is flexible the edge has infinite
capacity, and this bound is not imposed (`IsFeasibleFlow`). -/
noncomputable def flexCap (M : FisherMarket n g) (p : Fin g → ℝ) (j : Fin g) (i : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin (M.util i j).segs.length =>
      M.IsFlexibleSeg p (⟨j, k⟩ : M.Seg i)),
    M.segValue p (⟨j, k⟩ : M.Seg i)

/-- A feasible flow in the network `N(p)` on the vertices `{s} ∪ G ∪ B ∪ {t}`, recorded by its
values `y j i` on the good-to-buyer edges `(j, i)` (the flow on `(s, j)` is then `Σ_i y j i` and
the flow on `(i, t)` is `Σ_j y j i`, by conservation):
* `0 ≤ y j i ≤ flexCap p j i`, the capacity of the (merged) edge `(j, i)`, the upper bound
  dropped when the unbounded segment of `f^i_j` is flexible (infinite capacity);
* the edge `(s, j)` has capacity `unsold(j) · p_j`;
* the edge `(i, t)` has capacity `unspent(i)`. -/
def IsFeasibleFlow (M : FisherMarket n g) (p : Fin g → ℝ) (y : Fin g → Fin n → ℝ) : Prop :=
  (∀ j i, 0 ≤ y j i) ∧
    (∀ j i, ¬ M.IsFlexibleTail p i j → y j i ≤ M.flexCap p j i) ∧
    (∀ j, ∑ i, y j i ≤ M.unsold p j * p j) ∧
    (∀ i, ∑ j, y j i ≤ M.unspent p i)

/-- The max-flow value of `N(p)`: the supremum of the values `Σ_j Σ_i y j i` of feasible flows.
(When `p > 0`, `unsold(j) ≥ 0` and `unspent(i) ≥ 0` the zero flow is feasible and every value is
at most `Σ_i unspent(i)`, so this supremum is a maximum.) -/
noncomputable def maxFlow (M : FisherMarket n g) (p : Fin g → ℝ) : ℝ :=
  sSup {v | ∃ y, M.IsFeasibleFlow p y ∧ v = ∑ j, ∑ i, y j i}

end FisherMarket

end PLCMarkets.Rationality



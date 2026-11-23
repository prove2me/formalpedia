-- Prove2me | Definitions.Def_BinPacking_FirstFit_Supplement_ratioFFD
-- name    : BinPacking_FirstFit_Supplement_ratioFFD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:39:13.077794+00:00
-- url     : https://prove2.me/theorems/6fe6fa9c-b42c-445d-9a72-1176e856c471
-- title:
--   $R^\alpha_{FFD}(k)$: the worst-case ratio $FFD(L)/L^*$ over lists $L \subseteq (0, \alpha]$ with $L^* = k$
-- statement:
--   A **list** $L=(a_1,\dots,a_n)$ is a finite sequence of real numbers in $(0,1]$, repetitions allowed. Its optimum $L^*$ is the least number of unit-capacity bins into which its elements can be placed, and $FFD(L)$ is the number of bins used by **first-fit decreasing**: arrange $L$ into nonincreasing order and place each element, in that order, into the lowest-indexed bin whose current level $\beta$ satisfies $\beta\le 1-a_i$, opening a new bin if there is none.
--
--   For a real $\alpha$ and a natural number $k$, the **restricted worst-case ratio** of first-fit decreasing is
--
--   $$
--   R^\alpha_{FFD}(k)=\sup\Big\{\frac{FFD(L)}{L^*}\;:\;L \text{ a list with } a_i\le\alpha \text{ for every } i,\ L^*=k\Big\}.
--   $$
--
--   This is the paper's $R_{FFD}(k)$ ("the maximum value achieved by the ratio $FFD(L)/L^*$ over all lists with $L^*=k$", p. 301) with the lists restricted to $L\subseteq(0,\alpha]$, exactly as $R^\alpha_{FF}(k)$ and $R^\alpha_{BF}(k)$ are defined on p. 308; the paper uses $R^\alpha_{FFD}$ in §§3–4 (p. 315, p. 322). It is the quantity whose limit as $k\to\infty$ Theorem 4.4 determines.
--
--   **Formalization Note** The supremum is taken in the extended nonnegative reals $[0,\infty]$, so an empty family gives $0$ and an unbounded family gives $\infty$ rather than a default real value. At $k=0$ the only admissible list is the empty list and the value is $0/0=0$. Lists, $L^*$ and $FFD$ are those of the published definition `BinPacking.Decreasing.Model` (first-fit on a stable merge sort into nonincreasing order).
--
--   Differences from the source:
--   - encoding: a real-valued maximum for positive k → an ℝ≥0∞ supremum, with value 0 at k = 0 and for empty families; reason: for k ≥ 1 and α > 0 the admissible family is nonempty, and Theorem 3.2 bounds the integer FFD bin counts at fixed k, so the supremum is an attained finite maximum; the extra boundary values do not affect Theorem 4.4.
-- source:
--   Johnson, Demers, Ullman, Garey, Graham, Worst-Case Performance Bounds for Simple One-Dimensional Packing Algorithms, SIAM J. Comput. 3(4) (1974), p. 301 (R_FFD(k)), p. 308 (R^α_A(k) 'defined analogously … for lists L ⊆ (0, α]'), p. 322 (R^α_FFD in Theorem 4.4)

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model

namespace BinPacking.FirstFit.Supplement

open scoped ENNReal

/-- `R^α_FFD(k)` (Johnson et al. 1974, p. 301, p. 308, p. 315): the supremum of the ratio
`FFD(L)/L*` over all lists `L ⊆ (0, α]` (lists of reals in `(0, 1]` all of whose elements are at
most `α`) with `L* = k`. It is taken in `ℝ≥0∞`, so an empty family gives `0` and an unbounded
family gives `⊤` rather than a junk real value. At `k = 0` the only admissible list is `[]`, and
the value is `0 / 0 = 0`. -/
noncomputable def ratioFFD (α : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ⨆ (L : List ℝ) (_ : BinPacking.Decreasing.IsList L) (_ : ∀ a ∈ L, a ≤ α)
    (_ : BinPacking.Decreasing.optBins L = k),
    (BinPacking.Decreasing.FFD L : ℝ≥0∞) / (k : ℝ≥0∞)

end BinPacking.FirstFit.Supplement



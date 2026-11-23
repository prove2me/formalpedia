-- Prove2me | Definitions.Def_SPPRevenue_SingleUnit_Supplement_Programs
-- name    : SPPRevenue_SingleUnit_Supplement_Programs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:10:15.032155+00:00
-- url     : https://prove2.me/theorems/24d24280-e012-48bd-8d0d-672ff3b0f25b
-- title:
--   Theorem 2, p. 17 — the programs (FR-n) and (FR-n-d), well-posed factor-revealing programs, Table 4
-- statement:
--   Objects of Theorem 2 (n-dependent single-unit bounds).
--
--   1. **Well-posed program.** A maximization program, described by the set $V\subseteq[0,\infty]$ of objective values of its feasible points, is *well posed* when its value $\sup V$ is attained (so the "max" of the program exists), positive and finite.
--   2. **(FR-n).** For $n\ge1$ let $q_n(y)=(1-y/n)^n$. A function $s:[0,\infty)\to\mathbb R$ is feasible when it is weakly decreasing, $0\le s(\tau)\le\min(1,1/\tau)$ for all $\tau\ge0$, and
--   $$\int_0^\infty\big(1-q_n(s(\tau))\big)\,d\tau\le1 .$$
--   Its objective is $\int_0^\infty s(\tau)\,d\tau$, and $\mathrm{FR}(n)$ is the supremum of the objective over feasible $s$.
--   3. **(FR-n-d).** For $k\ge1$ let $s_i=i/k$, $i\in[k]$. A vector $w\in\mathbb R^k$ is feasible when $w_i\ge0$,
--   $$\sum_{i=j+1}^k w_i\frac{s_j}{s_i}\le1\quad(j\in[k-1]),\qquad \sum_{i=1}^k w_i\frac{1-q_n(s_i)}{s_i}\le1,$$
--   and $\mathrm{FR\text{-}d}(n,k)$ is the supremum of $\sum_i w_i$.
--   4. **Rounding.** A real $x$ rounds to $d/10^4$ when $d/10^4-1/(2\cdot10^4)\le x<d/10^4+1/(2\cdot10^4)$.
--   5. **Table 4.** The forty triples $(n,k,d)$ of Table 4, for $n\in[10]$ and $k\in\{200,400,800,1600\}$, where $d/10^4$ is the printed value of $1/\mathrm{FR\text{-}d}(n,k)$.
--
--   These programs give the approximation factors $1/\mathrm{FR}(n)$ and $1/\mathrm{FR\text{-}d}(n,k)$ of Theorem 2.
--
--   **Formalization Note** Values of programs are suprema in $[0,\infty]$; theorems state attainment, positivity and finiteness separately. The constraint $s\le\min(1,1/\tau)$ is written $s(\tau)\le1$ and $\tau s(\tau)\le1$, which agrees with the source at every $\tau\ge0$ and avoids Lean's $1/0=0$. Indices are 0-based: index $i$ of `Fin k` is the paper's $i+1$, so $s_i$ is `gridPt k i` $=(i+1)/k$.
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, pp. 16–17, Theorem 2, (FR-n), (FR-n-d), Table 4

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting

namespace SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

/-- A factor-revealing program, given by its set `V` of attainable objective values, is well posed
when its value `sup V` is attained (the program's `max` exists), positive and finite. -/
def IsFactorProgram (V : Set ℝ≥0∞) : Prop :=
  IsGreatest V (sSup V) ∧ 0 < sSup V ∧ sSup V ≠ ⊤

/-- Feasibility for (FR-n) (Theorem 2, p. 17): `s` weakly decreasing on `τ ≥ 0`,
`0 ≤ s(τ) ≤ min(1, 1/τ)` (written `s τ ≤ 1 ∧ τ * s τ ≤ 1`, which avoids `1/0 = 0` at `τ = 0`), and
`∫_0^∞ (1 − q_n(s(τ))) dτ ≤ 1` with `q_n(y) = (1 − y/n)^n`. -/
def FRNFeasible (n : ℕ) (s : ℝ → ℝ) : Prop :=
  AntitoneOn s (Set.Ici 0) ∧
    (∀ τ, 0 ≤ τ → 0 ≤ s τ ∧ s τ ≤ 1 ∧ τ * s τ ≤ 1) ∧
    ∫⁻ τ in Set.Ici 0, ENNReal.ofReal (1 - qn n (s τ)) ≤ 1

/-- The objective values `∫_0^∞ s(τ) dτ` of the feasible points of (FR-n). -/
def frNValues (n : ℕ) : Set ℝ≥0∞ := frObj '' {s | FRNFeasible n s}

/-- `FR(n)`, the optimal value of (FR-n) (Theorem 2, p. 17). -/
noncomputable def frN (n : ℕ) : ℝ≥0∞ := sSup (frNValues n)

/-- The grid point `s_i = i/k` for `i ∈ [k]`; index `i : Fin k` is the paper's `i + 1`. -/
noncomputable def gridPt (k : ℕ) (i : Fin k) : ℝ := ((i : ℝ) + 1) / k

/-- Feasibility for the discretized program (FR-n-d) (Theorem 2, p. 17): `w_i ≥ 0`,
`Σ_{i=j+1}^k w_i s_j / s_i ≤ 1` for every `j ∈ [k − 1]`, and `Σ_{i=1}^k w_i (1 − q_n(s_i))/s_i ≤ 1`.
Indices are 0-based: paper index `j ∈ [k−1]` is `j : Fin k` with `j + 1 < k`, and `i > j` is `j < i`. -/
def FRNdFeasible (n k : ℕ) (w : Fin k → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧
    (∀ j : Fin k, (j : ℕ) + 1 < k →
      ∑ i ∈ Finset.univ.filter (fun i => j < i), w i * (gridPt k j / gridPt k i) ≤ 1) ∧
    ∑ i, w i * ((1 - qn n (gridPt k i)) / gridPt k i) ≤ 1

/-- The objective values `Σ_{i ∈ [k]} w_i` of the feasible points of (FR-n-d). -/
def frNdValues (n k : ℕ) : Set ℝ≥0∞ :=
  (fun w : Fin k → ℝ => ENNReal.ofReal (∑ i, w i)) '' {w | FRNdFeasible n k w}

/-- `FR-d(n, k)`, the optimal value of (FR-n-d) (Theorem 2, p. 17). -/
noncomputable def frNd (n k : ℕ) : ℝ≥0∞ := sSup (frNdValues n k)

/-- `x` rounds to `d / 10⁴` at four decimal places: `d/10⁴ − 1/(2·10⁴) ≤ x < d/10⁴ + 1/(2·10⁴)`. -/
def RoundsTo4 (x : ℝ) (d : ℕ) : Prop :=
  (d : ℝ) / 10000 - 1 / 20000 ≤ x ∧ x < (d : ℝ) / 10000 + 1 / 20000

/-- Table 4 (p. 17): entries `(n, k, d)`, the reported value of `1/FR-d(n,k)` being `d / 10⁴`. -/
def table4 : List (ℕ × ℕ × ℕ) :=
  [(1, 200, 10000), (1, 400, 10000), (1, 800, 10000), (1, 1600, 10000),
   (2, 200, 7585), (2, 400, 7586), (2, 800, 7586), (2, 1600, 7586),
   (3, 200, 7167), (3, 400, 7168), (3, 800, 7168), (3, 1600, 7168),
   (4, 200, 6988), (4, 400, 6989), (4, 800, 6990), (4, 1600, 6990),
   (5, 200, 6889), (5, 400, 6890), (5, 800, 6891), (5, 1600, 6891),
   (6, 200, 6826), (6, 400, 6827), (6, 800, 6828), (6, 1600, 6828),
   (7, 200, 6782), (7, 400, 6784), (7, 800, 6784), (7, 1600, 6785),
   (8, 200, 6750), (8, 400, 6752), (8, 800, 6752), (8, 1600, 6753),
   (9, 200, 6726), (9, 400, 6727), (9, 800, 6728), (9, 1600, 6728),
   (10, 200, 6706), (10, 400, 6708), (10, 800, 6708), (10, 1600, 6709)]

end SPPRevenue.SingleUnit.Supplement



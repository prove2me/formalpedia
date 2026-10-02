-- Prove2me | Definitions.Def_SennottDP_Fatou_Basic
-- name    : SennottDP_Fatou_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T11:25:24.212562+00:00
-- url     : https://prove2.me/theorems/b39c0c90-05c2-4596-a86e-2e62815ff99d
-- title:
--   Weighted sums of extended-real functions and approximating probability distributions
-- statement:
--   Two objects used throughout Sections A.1–A.2 of Sennott's appendix.
--
--   **Weighted sums.** Let $S$ be a countable set, $(P_j)_{j\in S}$ nonnegative weights with values in $[0,\infty]$, and $u : S \to [-\infty,\infty]$. Write $u^+ = \max(u,0)$ and $u^- = \max(-u,0)$. The weighted sum is
--   $$\sum_{j\in S} P_j\, u(j) \;=\; \sum_{j\in S} P_j\, u^+(j) \;-\; \sum_{j\in S} P_j\, u^-(j),$$
--   where both sums on the right are sums of nonnegative terms in $[0,\infty]$ and the book's convention $0\cdot\infty = 0$ is used. Whenever $\sum_j P_j u^-(j) < \infty$ (for instance when $u \ge -L$ and $\sum_j P_j = 1$) this is the value of the series in $(-\infty,\infty]$, independent of the order of summation; likewise in $[-\infty,\infty)$ when $\sum_j P_j u^+(j)<\infty$.
--
--   **Approximating distributions.** Let $(P_j)_{j\in S}$ be a probability distribution on $S$. A sequence of approximating distributions consists of
--
--   1. an increasing sequence $(S_N)$ of subsets of $S$ with $\bigcup_N S_N = S$;
--   2. for each $N$, a probability distribution $(P_j(N))_{j\in S_N}$ on $S_N$, that is $\sum_{j\in S_N} P_j(N) = 1$;
--   3. pointwise convergence $\lim_{N\to\infty} P_j(N) = P_j$ for every $j\in S$ (meaningful since each $j$ lies in $S_N$ for all large $N$).
--
--   These are hypotheses (i)–(iii) of Proposition A.2.5, and they are the approximating-distribution hypotheses under which the book's approximating-sequence method passes limits through expectations.
--
--   **Formalization Note** The weighted sum is `wsum P u`, with `P : S → ℝ≥0∞` and `u : S → EReal`; positive and negative parts are `EReal.toENNReal` of `u` and `-u`. When both parts have infinite weighted sum the book's series is undefined and `wsum` returns $-\infty$ (Lean's `⊤ - ⊤ = ⊥` in `EReal`); no statement of this mission uses that value. Approximating distributions are the `Prop`-valued structure `ApproxDist P SN Q` with `Q N j` $=P_j(N)$; values of `Q N j` for $j\notin S_N$ are never used, since sums over $S_N$ are written as sums over $S$ of the indicator of $S_N$ times `Q N`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 270 (convention 0·∞ = 0), p. 273 (sum of a series), pp. 277–278, Proposition A.2.5 (i)–(iii)

import Mathlib

open Filter Topology
open scoped ENNReal

namespace SennottDP.Fatou

/-- Sennott (1999), App. A.1–A.2, pp. 270–278: the weighted sum `∑_{j ∈ S} P_j u(j)` of an
extended-real function `u` against nonnegative weights `P`, with the book's convention
`0 · ∞ = 0` (p. 270, p. 275). It is the sum of the positive parts minus the sum of the negative
parts, `∑_j P_j u(j)⁺ − ∑_j P_j u(j)⁻`, each computed in `[0, ∞]`. Whenever the negative (or the
positive) parts have a finite weighted sum this is the book's value of the series, in
`(−∞, ∞]` (resp. `[−∞, ∞)`); when both are infinite the book's sum is undefined and the value
here is `⊤ − ⊤ = ⊥` (a junk value that no statement of this mission relies on). -/
noncomputable def wsum {S : Type*} (P : S → ℝ≥0∞) (u : S → EReal) : EReal :=
  ((∑' j, P j * (u j).toENNReal : ℝ≥0∞) : EReal) - ((∑' j, P j * (-u j).toENNReal : ℝ≥0∞) : EReal)

/-- Sennott (1999), Proposition A.2.5 (i)–(iii), pp. 277–278: approximating distributions.
(i) `(P_j)_{j ∈ S}` is a probability distribution on `S`; (ii) `(S_N)` is an increasing sequence
of subsets of `S` with `⋃_N S_N = S`; (iii) for each `N`, `(P_j(N))_{j ∈ S_N}` is a probability
distribution on `S_N`, and `lim_{N → ∞} P_j(N) = P_j` for every `j ∈ S`. Here `Q N j = P_j(N)`;
its values for `j ∉ S_N` are never used (every sum is restricted to `S_N`, and a fixed `j` lies
in `S_N` for all large `N`). -/
structure ApproxDist {S : Type*} (P : S → ℝ≥0∞) (SN : ℕ → Set S) (Q : ℕ → S → ℝ≥0∞) : Prop where
  /-- (i) `∑_{j ∈ S} P_j = 1` -/
  prob : ∑' j, P j = 1
  /-- (ii) `S_N ⊆ S_{N+1}` -/
  mono : Monotone SN
  /-- (ii) `⋃_N S_N = S` -/
  iUnion_eq : ⋃ N, SN N = Set.univ
  /-- (iii) `∑_{j ∈ S_N} P_j(N) = 1` -/
  prob_N : ∀ N, ∑' j, (SN N).indicator (Q N) j = 1
  /-- (iii) `lim_{N → ∞} P_j(N) = P_j` -/
  tendsto : ∀ j, Tendsto (fun N => Q N j) atTop (𝓝 (P j))

end SennottDP.Fatou



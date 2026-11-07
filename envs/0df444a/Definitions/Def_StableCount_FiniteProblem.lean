-- Prove2me | Definitions.Def_StableCount_FiniteProblem
-- name    : StableCount_FiniteProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:03.451328+00:00
-- url     : https://prove2.me/theorems/f431edc0-cbcf-41ed-bd9e-9d44fe8f6730
-- title:
--   The finite problem (P) with the telescoping tail (26)
-- statement:
--   Choose integers $N\ge 3$ and $M\ge N+2$. The unknowns are $h_1,\dots,h_N,C$, and every later weight is
--   $$
--   h_d=\frac{C}{d(d-1)}\qquad\text{for }d>N.
--   $$
--   A **feasible solution of (P)** satisfies
--   $h_1\ge\dots\ge h_N\ge C/(N(N+1))$, $C\ge 2+4/(N(N+3))$, conditions (H1), (H4), (H5), and
--
--   1. $\lambda(2h_d)\le H_d+h_2$ for $2\le d\le N+1$;
--   2. $\lambda(2h_a)+\lambda(h_{a-1}+2h_a+h_c)\le H_a+A_c$ for $3\le a<M$ and $1\le c\le N+1$;
--   3. $\lambda(2h_M)+\lambda(h_c)\le H_M+A_c$ for $1\le c\le N+1$.
--
--   This reduces admissibility, an infinite family of conditions, to finitely many inequalities.
--
--   **Formalization Note** The paper's (P) minimizes $S=\sum_{d\le N}h_d+C/N$. Only the constraints are encoded, since the statement about (P) concerns every feasible solution. $H_d$ and $A_c$ read the extended sequence.
-- source:
--   Ghorbani, Mnich, A 2.81^n upper bound on the number of stable matchings, arXiv:2611.06494 (held PDF sha256 9445f6a8…), (26), p.31; (P), p.32

import Mathlib
import Definitions.Def_StableCount_Potential

namespace StableCount

/-- The sequence extended by the telescoping tail: `h_d` is the given prefix value for `d ≤ N`, and
`h_d = C/(d(d − 1))` for `d > N`, display (26) (arXiv:2611.06494, held PDF sha256 9445f6a8…, (26), p.31). -/
noncomputable def extend (hs : ℕ → ℝ) (C : ℝ) (N d : ℕ) : ℝ :=
  if d ≤ N then hs d else C / ((d : ℝ) * ((d : ℝ) - 1))

/-- A feasible solution of the problem (P) for integers `N ≥ 3` and `M ≥ N + 2`, with unknowns
`h₁,…,h_N, C` and every later `h_d` given by (26) (arXiv:2611.06494, held PDF sha256 9445f6a8…, (P), p.32).

**Formalization Note** (P) minimizes `S`; only its constraints are encoded, since Proposition 9.2 is
about every feasible solution. Sums `H_d`, `A_c` read the extended sequence. -/
def IsFeasibleP (N M : ℕ) (hs : ℕ → ℝ) (C : ℝ) : Prop :=
  let h := extend hs C N
  (∀ d, 1 ≤ d → d < N → h (d + 1) ≤ h d) ∧ C / ((N : ℝ) * ((N : ℝ) + 1)) ≤ h N ∧
    2 + 4 / ((N : ℝ) * ((N : ℝ) + 3)) ≤ C ∧ CondH1 h ∧ CondH4 h ∧ CondH5 h ∧
    (∀ d, 2 ≤ d → d ≤ N + 1 → lam (2 * h d) ≤ Hsum h d + h 2) ∧
    (∀ a c, 3 ≤ a → a < M → 1 ≤ c → c ≤ N + 1 →
      lam (2 * h a) + lam (h (a - 1) + 2 * h a + h c) ≤ Hsum h a + Aval h c) ∧
    ∀ c, 1 ≤ c → c ≤ N + 1 → lam (2 * h M) + lam (h c) ≤ Hsum h M + Aval h c

end StableCount



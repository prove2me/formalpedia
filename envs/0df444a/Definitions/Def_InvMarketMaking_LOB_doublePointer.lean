-- Prove2me | Definitions.Def_InvMarketMaking_LOB_doublePointer
-- name    : InvMarketMaking_LOB_doublePointer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:18:50.280296+00:00
-- url     : https://prove2.me/theorems/22e63aa6-f5aa-42dc-8608-aee75e8316c9
-- title:
--   Algorithm 5 (Double Double Pointer)
-- statement:
--   **Algorithm 5** takes the active bids $b_0<\dots<b_{N-1}$, the active asks $a_0<\dots<a_{M-1}$ and confidence bounds $F^{\mathrm{up}},F^{\mathrm{low}},S^{\mathrm{up}},S^{\mathrm{low}}$, and returns a candidate pair.
--
--   1. *First scan.* Set $J^{\mathrm{low}}=0$ and $m=M-1$. For $n=0,\dots,N-1$: while $m\ge0$ and $b_n<a_m$, set $J^{\mathrm{low}}\leftarrow\max\{J^{\mathrm{low}},(a_m-b_n)\min(F^{\mathrm{low}}(b_n),S^{\mathrm{low}}(a_m))\}$; then, if $F^{\mathrm{low}}(b_n)<S^{\mathrm{low}}(a_m)$, leave the while loop (so $n$ advances and $m$ is kept), otherwise set $m\leftarrow m-1$.
--   2. *Second scan.* Set $n=0$, $m=M-1$. While $n<N$, $m\ge0$ and $b_n<a_m$: if $(a_m-b_n)\min\{F^{\mathrm{up}}(b_n),S^{\mathrm{up}}(a_m)\}\ge J^{\mathrm{low}}$, return $(b_n,a_m)$; otherwise, if $F^{\mathrm{up}}(b_n)<S^{\mathrm{up}}(a_m)$ set $n\leftarrow n+1$, else $m\leftarrow m-1$.
--
--   The first scan computes the best certified (lower-bound) value among feasible pairs; the second returns the first pair, scanning from the outside in, whose optimistic value reaches it.
--
--   **Formalization Note** The loops run on fuel $N+M+1$, which is never exhausted. The paper gives no return value if the second loop ends without returning; this definition then returns the outer pair $(b_0,a_{M-1})$ (with $0$ for an empty list). Proposition 6.11 shows this case does not occur on grids containing a pair $b<a$ with nonnegative radii.
-- source:
--   Maran, Restelli, Stradi, No-Regret Revenue Maximization in Sequential Market Making Under Inventory Constraints, arXiv:2610.24562v1, Algorithm 5, p. 38

import Mathlib

namespace InvMarketMaking.LOB

/-- The first scan of Algorithm 5 (Lines 1–13): computes `J^low`. The arguments after the
bounds are the fuel, the bid index `n`, `k = m + 1` (so `k = 0` encodes `m = −1`) and the current
value of `J^low`. For each `n`, the inner `while m ≥ 0 and b_n < a_m` loop updates
`J^low ← max{J^low, (a_m − b_n) min(F^low(b_n), S^low(a_m))}`, then `break`s (the `for` loop
advances `n`, `m` unchanged) if `F^low(b_n) < S^low(a_m)`, and otherwise sets `m ← m − 1`. -/
noncomputable def firstScan (bids asks : List ℝ) (Flo Slo : ℝ → ℝ) : ℕ → ℕ → ℕ → ℝ → ℝ
  | 0, _, _, Jl => Jl
  | fuel + 1, n, k, Jl =>
    if n < bids.length then
      if 0 < k ∧ bids.getD n 0 < asks.getD (k - 1) 0 then
        if Flo (bids.getD n 0) < Slo (asks.getD (k - 1) 0) then
          firstScan bids asks Flo Slo fuel (n + 1) k
            (max Jl ((asks.getD (k - 1) 0 - bids.getD n 0) *
              min (Flo (bids.getD n 0)) (Slo (asks.getD (k - 1) 0))))
        else
          firstScan bids asks Flo Slo fuel n (k - 1)
            (max Jl ((asks.getD (k - 1) 0 - bids.getD n 0) *
              min (Flo (bids.getD n 0)) (Slo (asks.getD (k - 1) 0))))
      else firstScan bids asks Flo Slo fuel (n + 1) k Jl
    else Jl

/-- The second scan of Algorithm 5 (Lines 14–26). The arguments after `J^low` are the fuel, the
bid index `n` and `k = m + 1`. While `n < N`, `m ≥ 0` and `b_n < a_m`: return `(b_n, a_m)` if
`(a_m − b_n) min{F^up(b_n), S^up(a_m)} ≥ J^low`; otherwise `n ← n + 1` if
`F^up(b_n) < S^up(a_m)`, else `m ← m − 1`. `none` means the loop exited without returning. -/
noncomputable def secondScan (bids asks : List ℝ) (Fup Sup : ℝ → ℝ) (Jl : ℝ) :
    ℕ → ℕ → ℕ → Option (ℝ × ℝ)
  | 0, _, _ => none
  | fuel + 1, n, k =>
    if n < bids.length ∧ 0 < k ∧ bids.getD n 0 < asks.getD (k - 1) 0 then
      if Jl ≤ (asks.getD (k - 1) 0 - bids.getD n 0) *
          min (Fup (bids.getD n 0)) (Sup (asks.getD (k - 1) 0)) then
        some (bids.getD n 0, asks.getD (k - 1) 0)
      else if Fup (bids.getD n 0) < Sup (asks.getD (k - 1) 0) then
        secondScan bids asks Fup Sup Jl fuel (n + 1) k
      else
        secondScan bids asks Fup Sup Jl fuel n (k - 1)
    else none

/-- **Algorithm 5** (Double Double Pointer) of Maran, Restelli, Stradi, arXiv:2610.24562v1, p. 38.
Input: the active bids `b_0 < … < b_{N−1}` and active asks `a_0 < … < a_{M−1}` as increasing lists,
and the confidence bounds `F^up, F^low, S^up, S^low`. Output: the candidate pair `(B_{t,0}, A_{t,0})`.

**Formalization Note** The two `while` loops are run with fuel `N + M + 1`; each step increases
`n` or decreases `m`, so the fuel never runs out before the loops stop. The pseudocode has no
return statement after the second loop (Line 26); in that case this definition returns the outer
pair `(b_0, a_{M−1})` (with `0` for an empty list). By Proposition 6.11 this fallback is never
reached on grids containing a pair `b < a` with nonnegative radii. -/
noncomputable def doublePointer (bids asks : List ℝ) (Fup Flo Sup Slo : ℝ → ℝ) : ℝ × ℝ :=
  match secondScan bids asks Fup Sup
      (firstScan bids asks Flo Slo (bids.length + asks.length + 1) 0 asks.length 0)
      (bids.length + asks.length + 1) 0 asks.length with
  | some p => p
  | none => (bids.getD 0 0, asks.getD (asks.length - 1) 0)

end InvMarketMaking.LOB



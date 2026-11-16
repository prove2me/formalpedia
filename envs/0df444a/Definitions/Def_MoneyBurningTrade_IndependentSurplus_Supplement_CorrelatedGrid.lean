-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_CorrelatedGrid
-- name    : MoneyBurningTrade_IndependentSurplus_Supplement_CorrelatedGrid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:36:05.981183+00:00
-- url     : https://prove2.me/theorems/7b36eae9-b0aa-41f8-911b-f1bc391c86f9
-- title:
--   Equation (22) — the fast-growing grid of §4.3
-- statement:
--   For an integer $n$ (in §4.3, $n\ge4$), let $\delta=1/(100n)$ and
--
--   $$q_i=\frac{\delta^{\,n-i}-\delta^{\,n}}{1-\delta^{\,n}}\qquad(i=0,1,\dots,n).$$
--
--   Then $q_0=0$, $q_n=1$, and the gaps $L_i=q_i-q_{i-1}=(1-\delta)\delta^{n-i}/(1-\delta^n)$ grow by the factor $1/\delta$ from left to right. For $2\le i\le n-2$ put $\Delta_i=q_{i+1}-q_{i-1}$ and
--
--   $$C=\frac{1}{\sum_{r=2}^{n-2}1/\Delta_r}.$$
--
--   This grid (not the symmetric grid (20) of §4.2) underlies the correlated separation of Theorem 4.2.
--
--   **Formalization Note** The grid is a published `Grid` with length $n$; its entries beyond index $n$ are unused and set to $1$.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), §4.3, equation (22) and the definitions of Δ_i and C, printed p. 30 (PDF p. 31); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Grid

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- `δ = 1/(100n)`, §4.3 p.30. -/
noncomputable def corrDelta (n : ℕ) : ℝ := 1 / (100 * (n : ℝ))

/-- The grid of equation (22), §4.3 p.30:
`q_i = (δ^(n−i) − δ^n)/(1 − δ^n)` for `i ∈ {0,…,n}`, with `δ = 1/(100n)`.
Indices beyond `n` are unused; they are set to `1`. -/
noncomputable def correlatedGrid (n : ℕ) : Grid where
  n := n
  q := fun i => if i ≤ n then
    (corrDelta n ^ (n - i) - corrDelta n ^ n) / (1 - corrDelta n ^ n) else 1

/-- `Δ_i = q_{i+1} − q_{i−1}`, §4.3 p.30 (used for `2 ≤ i ≤ n − 2`). -/
noncomputable def corrSpread (n i : ℕ) : ℝ :=
  (correlatedGrid n).q (i + 1) - (correlatedGrid n).q (i - 1)

/-- `C = 1 / Σ_{r=2}^{n−2} 1/Δ_r`, §4.3 p.30. -/
noncomputable def corrC (n : ℕ) : ℝ :=
  1 / ∑ r ∈ Finset.Icc 2 (n - 2), 1 / corrSpread n r

end MoneyBurningTrade.IndependentSurplus.Supplement



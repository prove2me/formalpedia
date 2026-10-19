-- Prove2me | Definitions.Def_InnovContest_Rewards_OrderStats
-- name    : InnovContest_Rewards_OrderStats
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:56.105848+00:00
-- url     : https://prove2.me/theorems/0bb0dcb1-873d-4d1a-9fa1-a67f5e4bfe1f
-- title:
--   Order-statistic CDF and density for independent abilities
-- statement:
--   For $n$ independent draws with common CDF $F$ and density $f$, let $F_{j:n}$ and $f_{j:n}$ denote the CDF and density of the $j$th smallest draw. For $q=F(a)$, the definitions are
--
--   $$F_{j:n}(a)=\sum_{i=j}^{n}\binom ni q^i(1-q)^{n-i},\qquad f_{j:n}(a)=n\binom{n-1}{j-1}F(a)^{j-1}(1-F(a))^{n-j}f(a).$$
--
--   These common order-statistic objects determine the probability that a solver receives each performance rank. The finite sum is zero when $j>n$; for $q\in[0,1]$, it is one when $j=0$.
-- source:
--   Stouras, Hutchison-Krupat & Chao, The Role of Participation in Innovation Contests, SSRN 2924224 (accepted version), p. ec1 (PDF 35), equations (EC.1)–(EC.2)

import Mathlib

namespace InnovContest.Rewards

/-- The CDF of the `j`-th smallest among `n` independent draws whose common CDF has value `q`.
For `0 ≤ q ≤ 1`, `ordCDF n 0 q = 1` and `ordCDF n (n+1) q = 0`. -/
def ordCDF (n j : ℕ) (q : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc j n, (n.choose i : ℝ) * q ^ i * (1 - q) ^ (n - i)

/-- The density of the `j`-th smallest of `n` independent draws with CDF `F` and density `f`. -/
def ordPDF (n j : ℕ) (F f : ℝ → ℝ) (a : ℝ) : ℝ :=
  (n : ℝ) * ((n - 1).choose (j - 1) : ℝ) *
    F a ^ (j - 1) * (1 - F a) ^ (n - j) * f a

end InnovContest.Rewards



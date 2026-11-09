-- Prove2me | Definitions.Def_RecruitSmaller_Delta
-- name    : RecruitSmaller_Delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:47.504104+00:00
-- url     : https://prove2.me/theorems/e607475a-377d-456f-80dd-f203d051d792
-- title:
--   Seller-indicator difference $\Delta_{n,k,i}(x,y)$
-- statement:
--   For $n$ and $k$ sellers with costs i.i.d. with CDF $F_S$, a rank $i$ and reals $x,y$,
--   $$
--   \Delta_{n,k,i}(x,y) := \Pr_{s_k}\bigl[s^{(i)}_k\le x \text{ and } s^{(i+1)}_k\le y\bigr]-\Pr_{s_n}\bigl[s^{(i)}_n\le x\bigr].
--   $$
--   In the paper the second argument is the buyer order statistic $b^{(i)}$; the rank-$i$ comparison of Lemma 3.3 integrates $\Delta_{n,k,i}(x,b^{(i)})\,\mathbb 1[b^{(i)}\ge x]$ over thresholds $x$.
--
--   **Formalization Note** The probabilities are real values of the product measures $\mu_S^{\otimes k}$, $\mu_S^{\otimes n}$.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.3, eq. (3.6), p.12

import Mathlib
import Definitions.Def_RecruitSmaller_sellerOrd

open MeasureTheory

namespace RecruitSmaller

/-- The **seller-indicator difference** (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma 3.3, eq. (3.6), p.12):
`Δ_{n,k,i}(x, y) := Pr_{sₖ}[s⁽ⁱ⁾ₖ ≤ x and s⁽ⁱ⁺¹⁾ₖ ≤ y] − Pr_{sₙ}[s⁽ⁱ⁾ₙ ≤ x]`, for `k` and `n`
seller costs i.i.d. from `μS`.

**Formalization Note** The page writes the second argument as `b⁽ⁱ⁾`; `Δ` depends only on its value
`y`. Probabilities are `toReal` of the product measures `μSᵏ`, `μSⁿ` (finite for a probability
measure). -/
noncomputable def Delta (μS : Measure ℝ) (n k i : ℕ) (x y : ℝ) : ℝ :=
  ((Measure.pi fun _ : Fin k => μS) {s | sellerOrd s i ≤ x ∧ sellerOrd s (i + 1) ≤ y}).toReal -
    ((Measure.pi fun _ : Fin n => μS) {s | sellerOrd s i ≤ x}).toReal

end RecruitSmaller



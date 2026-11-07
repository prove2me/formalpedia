-- Prove2me | Definitions.Def_AvgPHETH_LDown
-- name    : AvgPHETH_LDown
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:58.36017+00:00
-- url     : https://prove2.me/theorems/17d5e3ed-c931-4016-b199-a54f3c17b4e7
-- title:
--   The class $\mathcal L_{\downarrow k}(m(n))$ of logarithmic savings
-- statement:
--   For a length function $m$ with $m(n)\ge2$ for sufficiently large $n$ and a fixed integer $k\ge0$, $\mathcal L_{\downarrow k}(m(n))$ is the class of polynomial-time computable integer-valued length functions $\ell$ with
--
--   $$\ell(n)=\Theta\!\left(\frac{m(n)}{(\log m(n))^k}\right).$$
--
--   We write $\mathcal L_{\downarrow k}$ for $\mathcal L_{\downarrow k}(n)$. These classes keep track of the logarithmic factors saved by compressing moves.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Definition 4.9, p.19 (PDF 21)

import Mathlib
import Definitions.Def_AvgPHETH_IsPolyLen

namespace AvgPHETH

/-- The class `𝓛_{↓k}(m(n))` of length functions with `k` logarithmic savings
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Definition 4.9, p.19 (PDF 21)): for a length function `m` with `m(n) ≥ 2` for sufficiently
large `n`, the polynomial-time computable integer-valued `ℓ` with `ℓ(n) = Θ(m(n)/(log m(n))^k)`.
`𝓛_{↓k} = LDown k id`.

**Formalization Note** The definition's assumption on `m` is a clause of the class, so the class is empty
for any other `m`, and no junk value of `log` is ever used. `log` is base 2. -/
def LDown (k : ℕ) (m : ℕ → ℕ) : Set (ℕ → ℕ) :=
  {ℓ | (∃ n₀ : ℕ, ∀ n ≥ n₀, 2 ≤ m n) ∧ IsPolyLen ℓ ∧ ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
    a * (m n : ℝ) / Real.logb 2 (m n : ℝ) ^ k ≤ (ℓ n : ℝ) ∧
      (ℓ n : ℝ) ≤ A * (m n : ℝ) / Real.logb 2 (m n : ℝ) ^ k}

end AvgPHETH



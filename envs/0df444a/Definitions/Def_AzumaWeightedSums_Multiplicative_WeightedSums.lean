-- Prove2me | Definitions.Def_AzumaWeightedSums_Multiplicative_WeightedSums
-- name    : AzumaWeightedSums_Multiplicative_WeightedSums
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:07:38.751081+00:00
-- url     : https://prove2.me/theorems/4b1d197f-6d00-47ab-9e44-d91bc2bd1176
-- title:
--   Triangular weighted sum $T_n$ and weight norm $B_n$
-- statement:
--   Given a real triangular array of weights $(a_{nk})_{1\le k\le n}$ and real random variables $(x_k)_{k\ge1}$, define the **weighted sum** $T_n$ and its **weight norm** $B_n$ by
--
--   $$
--   T_n=\sum_{k=1}^{n}a_{nk}x_k,
--   \qquad
--   B_n=\left(\sum_{k=1}^{n}a_{nk}^{2}\right)^{1/2}.
--   $$
--
--   The array may change with $n$. These are the two quantities in Azuma's first almost-sure limit theorem; no nonzero-weight or growth condition is built into their definitions.
--
--   **Formalization Note** The range is exactly $k=1,\ldots,n$. At $n=0$ the empty sum and $B_0$ are zero.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), p. 359, §3, first paragraph, https://doi.org/10.2748/tmj/1178243286

import Mathlib

namespace AzumaWeightedSums.Multiplicative

/-- Azuma (1967), p. 359, §3: `Tₙ = ∑_{k=1}^n aₙₖ xₖ`. -/
def weightedSum {Ω : Type*} (a : ℕ → ℕ → ℝ) (x : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, a n k * x k ω

/-- Azuma (1967), p. 359, §3: `Bₙ = (∑_{k=1}^n aₙₖ²)^(1/2)`. -/
noncomputable def weightNorm (a : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (∑ k ∈ Finset.Icc 1 n, (a n k) ^ 2)

end AzumaWeightedSums.Multiplicative



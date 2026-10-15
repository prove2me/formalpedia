-- Prove2me | Definitions.Def_VehicleSharePricing_MultiNet_GenBinom
-- name    : VehicleSharePricing_MultiNet_GenBinom
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:29:43.599469+00:00
-- url     : https://prove2.me/theorems/9eb051e0-d217-46d1-8087-534849209aa1
-- title:
--   p. 18 — binomial coefficient with a real upper argument, $\binom{x}{k}=\prod_{i=0}^{k-1}(x-i)/k!$
-- statement:
--   For a real number $x$ and a natural number $k$, the binomial coefficient used on p. 18 of Benjaafar and Shen is
--   $$\binom{x}{k}=\frac{\prod_{i=0}^{k-1}(x-i)}{k!},$$
--   so that $\binom{x}{0}=1$. The paper applies it with $x=K+T-1$, $T$ a positive real, in its use of the Chu–Vandermonde identity.
--
--   **Formalization Note** The page also sets $\binom{x}{k}=0$ for $k<0$; since $k$ is a natural number here, that clause is not needed. The definition agrees with Mathlib's `Ring.choose` on $\mathbb R$, but is written with the page's own formula.
-- source:
--   Benjaafar & Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN abstract 3998297 (version of 2023-01-10), p. 18, §6, proof of Theorem 4 (definition of the binomial coefficient)

import Mathlib

namespace VehicleSharePricing.MultiNet

open Finset

/-- The binomial coefficient with a real upper argument, as defined on p. 18:
`C(x, k) = ∏_{i=0}^{k-1} (x - i) / k!` for `k ≥ 0` (the empty product gives `C(x, 0) = 1`).
The page's convention `C(x, k) = 0` for `k < 0` is not needed, since `k : ℕ`. -/
noncomputable def gbinom (x : ℝ) (k : ℕ) : ℝ :=
  (∏ i ∈ Finset.range k, (x - (i : ℝ))) / (k.factorial : ℝ)

end VehicleSharePricing.MultiNet



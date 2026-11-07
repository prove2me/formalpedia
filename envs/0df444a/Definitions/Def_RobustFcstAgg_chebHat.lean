-- Prove2me | Definitions.Def_RobustFcstAgg_chebHat
-- name    : RobustFcstAgg_chebHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:42:04.526199+00:00
-- url     : https://prove2.me/theorems/5bd6544e-cdb8-4cdd-98fe-f71b90ead01b
-- title:
--   The transformed Chebyshev polynomial $\hat T_d$
-- statement:
--   With $T_d$ the Chebyshev polynomial of order $d$ and $m(x)=\frac{2x-(n+1)}{n-1}$ the affine map of $[1,n]$ onto $[-1,1]$,
--   $$\hat T_d(x)=\frac{T_d(m(x))}{T_d(m(0))}.$$
--   It is the extremal polynomial of the interval problem.
--
--   **Formalization Note** For $n\ge2$, $|m(0)|=\frac{n+1}{n-1}>1$, so the denominator does not vanish.
-- source:
--   Frongillo–Monroe–Neyman–Waggoner, Robust Forecast Aggregation via Additional Queries, arXiv:2512.05271, proof of Lemma 10, p.29

import Mathlib
open Polynomial

namespace RobustFcstAgg

/-- **The transformed Chebyshev polynomial `T̂_d`.** Frongillo–Monroe–Neyman–Waggoner, *Robust Forecast Aggregation via Additional Queries*, arXiv:2512.05271, proof of Lemma 10, p.29: `T̂_d(x) = T_d(m(x)) / T_d(m(0))` with
`m(x) = (2x − (n+1))/(n−1)`.

**Formalization Note.** `T_d` is `Polynomial.Chebyshev.T ℝ d`. For `n ≥ 2`, `|m(0)| = (n+1)/(n−1) > 1`, so `T_d(m(0)) ≠ 0`
and the inversion is genuine. Lemma 10 is the only statement using this and assumes `2 ≤ n`. -/
noncomputable def chebHat (n d : ℕ) : ℝ[X] :=
  let m : ℝ[X] := C (2 / ((n : ℝ) - 1)) * X - C (((n : ℝ) + 1) / ((n : ℝ) - 1))
  C ((Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (m.eval 0))⁻¹ * (Polynomial.Chebyshev.T ℝ (d : ℤ)).comp m

end RobustFcstAgg



-- Prove2me | Definitions.Def_ParetoNCSched_cR
-- name    : ParetoNCSched_cR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:26.610201+00:00
-- url     : https://prove2.me/theorems/b65faf12-c4bc-41ff-a6ba-9a8f188fb9bd
-- title:
--   The consistency $c(R)=R\big(1-(1-\frac{R+2}{R^2})^{R/(R+2)}\big)$
-- statement:
--   For $R>2$,
--   $$c(R)=R\left(1-\left(1-\frac{R+2}{R^2}\right)^{\frac{R}{R+2}}\right).$$
--   This is the consistency of the Maximal Robust Commitment algorithm $\mathrm{MRC}_R$, equation (1) of the paper. For $R>2$ the base equals $(R+1)(R-2)/R^2\in(0,1)$.
--
--   **Formalization Note** The power is the real power function.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Theorem 1.1, Eq. (1), p.4

import Mathlib

namespace ParetoNCSched

/-- **The consistency `c(R)`**, equation (1). Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Theorem 1.1, p.4:
"c(R) = R (1 − (1 − (R + 2)/R²)^(R/(R+2)))".

**Formalization Note.** The power is `Real.rpow`. For `R > 2` the base equals `(R+1)(R−2)/R²`,
which lies in `(0, 1)`. -/
noncomputable def cR (R : ℝ) : ℝ :=
  R * (1 - (1 - (R + 2) / R ^ 2) ^ (R / (R + 2)))

end ParetoNCSched



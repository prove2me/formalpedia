-- Prove2me | Definitions.Def_PRUPermLayer_gammaT
-- name    : PRUPermLayer_gammaT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:52.026313+00:00
-- url     : https://prove2.me/theorems/26546191-fdce-4fcd-b48a-29d8e00926ec
-- title:
--   $\gamma_t = t(t-1)/(N-t+1)$
-- statement:
--   For integers $N, t$,
--   $$
--   \gamma_t = \frac{t(t-1)}{N - t + 1} .
--   $$
--   It bounds the squared Friedrichs cosine of $\mathrm{Dist}_{N,t}$ and $\mathrm{NoPlus}_{N,t}$ (Fact 2.3).
--
--   **Formalization Note** Computed in the reals; the denominator is positive whenever $t \le N/2$, the range where it is used. Example: $N = 4$, $t = 2$ gives $2/3$.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Fact 2.3, p.10 (PDF p.12)

import Mathlib

namespace PRUPermLayer

/-- `γ_t = t(t − 1)/(N − t + 1)` (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Fact 2.3, p.10 (PDF p.12)).

**Formalization Note** Computed in `ℝ`; the denominator `N − t + 1` is positive in every range
where it is used (`t ≤ N/2`). Example: `gammaT 4 2 = 2/3`. -/
noncomputable def gammaT (N t : ℕ) : ℝ := (t : ℝ) * ((t : ℝ) - 1) / ((N : ℝ) - t + 1)

end PRUPermLayer



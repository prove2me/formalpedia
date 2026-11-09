-- Prove2me | Definitions.Def_PinwheelDensity_ExactRange_coreP
-- name    : PinwheelDensity_ExactRange_coreP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:52.17627+00:00
-- url     : https://prove2.me/theorems/55298432-a496-40fe-9743-86dcb46edb09
-- title:
--   The families $P_n$, $Q_m$, the sharpness cores and $g(m)$
-- statement:
--   The notation $b^{[r]}$ means $r$ copies of the period $b$. The mission uses the sharpness core $(m,(m+1)^{[m-1]})$ for $m\ge1$, the core
--   $$P_n=(n-1,\ n^{[n-3]},\ 2n-1,\ 4n-1,\ 5n)\qquad(n\ge3),$$
--   the core
--   $$Q_m=(m,\ m,\ (m+1)^{[m-3]},\ 2m+2,\ 3m+2)\qquad(m\ge4),$$
--   and the first refutation family $(m,(m+1)^{[m-2]},2m+1,4m+3,5m+5,x)$, which is $P_{m+1}+(x)$. With $n=m+1$,
--   $$g(m)=\frac{2(n^2-7n+2)}{5n(2n-1)(4n-1)},$$
--   and the second family's threshold on $x$ is $2m(m+1)(3m+2)/(m^2-6m-4)$.
--
--   These explicit lists are the counterexamples behind the negative half of the exact range.
--
--   **Formalization Note** Natural subtraction appears only in list lengths and entries, and is exact in the stated ranges $n\ge3$, $m\ge4$, $m\ge6$. The rational expressions are computed after coercion to `ℚ`.
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Theorem 1.4, p. 2; Section 2.1, p. 4; Lemma 2.4, p. 4; Lemma 2.6, p. 7 (same PDF pages)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable

namespace PinwheelDensity.ExactRange

/-- The sharpness core `(m, (m + 1)^[m - 1])` of Section 2.1, p. 4, used for `m ≥ 1`.
`List.replicate r b` is the source's `b^[r]`: `r` copies, never a power. -/
def sharpCore (m : ℕ) : List ℕ :=
  m :: List.replicate (m - 1) (m + 1)

/-- `Pₙ = (n - 1, n^[n - 3], 2n - 1, 4n - 1, 5n)` of Lemma 2.4, p. 4, used for `n ≥ 3`. -/
def coreP (n : ℕ) : List ℕ :=
  (n - 1) :: List.replicate (n - 3) n ++ [2 * n - 1, 4 * n - 1, 5 * n]

/-- `Qₘ = (m, m, (m + 1)^[m - 3], 2m + 2, 3m + 2)` of Lemma 2.6, p. 7, used for `m ≥ 4`. -/
def coreQ (m : ℕ) : List ℕ :=
  m :: m :: List.replicate (m - 3) (m + 1) ++ [2 * m + 2, 3 * m + 2]

/-- The first family of Theorem 1.4, p. 2: `(m, (m + 1)^[m - 2], 2m + 1, 4m + 3, 5m + 5, x)`. -/
def refutationP (m x : ℕ) : List ℕ :=
  m :: List.replicate (m - 2) (m + 1) ++ [2 * m + 1, 4 * m + 3, 5 * m + 5, x]

/-- `g(m) = 2 (n² - 7n + 2) / (5 n (2n - 1) (4n - 1))` with `n = m + 1` (Theorem 1.4, p. 2),
computed in `ℚ`; the denominator is positive for every natural `m`. -/
def g (m : ℕ) : ℚ :=
  let n : ℚ := (m : ℚ) + 1
  2 * (n ^ 2 - 7 * n + 2) / (5 * n * (2 * n - 1) * (4 * n - 1))

/-- `2m(m + 1)(3m + 2)/(m² - 6m - 4)`, the bound on `x` of Theorem 1.4, p. 2, used for `m ≥ 7`,
where the denominator is positive. -/
def qThreshold (m : ℕ) : ℚ :=
  2 * (m : ℚ) * ((m : ℚ) + 1) * (3 * (m : ℚ) + 2) / ((m : ℚ) ^ 2 - 6 * (m : ℚ) - 4)

end PinwheelDensity.ExactRange



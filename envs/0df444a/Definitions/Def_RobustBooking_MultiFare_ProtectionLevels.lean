-- Prove2me | Definitions.Def_RobustBooking_MultiFare_ProtectionLevels
-- name    : RobustBooking_MultiFare_ProtectionLevels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T23:24:35.852807+00:00
-- url     : https://prove2.me/theorems/69cf58db-1755-445d-bcce-954388697837
-- title:
--   Δ (Eq. 6), protection levels θ (Eq. 7), controls Q (Eqs. 8–9) and the order quantity control function P
-- statement:
--   Let $f_1 > f_2 > \dots > f_m > 0$ be the fares of $m$ classes and $n > 0$ the capacity. Ball and Queyranne define (p. 957)
--   $$\Delta = m - \sum_{i=2}^{m} \frac{f_i}{f_{i-1}} \qquad \text{(Eq. (6))},$$
--   the **protection levels**
--   $$\theta_i = \frac{n}{\Delta}\Bigl(i - \sum_{j=1}^{i} \frac{f_{j+1}}{f_j}\Bigr) \quad (i = 1, \dots, m-1) \qquad \text{(Eq. (7))}, \qquad \theta_m = n,$$
--   with $\theta_0 = 0$, the **protection-level controls**
--   $$Q_i = n - \theta_{i-1} \quad (i = 1, \dots, m+1) \qquad \text{(Eq. (8))}, \qquad Q_1 = n \qquad \text{(Eq. (9))},$$
--   so that $Q_{m+1} = 0$, and the **order quantity control function** on $0 \le q \le n$:
--   $$P(q) = f_i \ \text{ for } Q_{i+1} < q \le Q_i,\ 1 \le i \le m, \qquad P(0) = 0.$$
--   $Q_i$ is the most that may be sold in total to the classes $i, i+1, \dots, m$ (fares at most $f_i$), and $P(q)$ is the lowest fare still accepted once $q$ units are sold.
--
--   **Formalization Note.** Indices are natural numbers, read 1-based. `theta` returns $0$ at $i = 0$, formula (7) for $1 \le i < m$, and $n$ for $i \ge m$ (only $i = m$ is used). `Q i = n - theta (i - 1)` for $i \ge 1$; the index $0$ is unused. Q is defined from Eqs. (8)–(9), not from the text's "$Q(f) = n - \theta(f)$" with "$\theta_i = \theta(f_i)$", which is off by one index. For $0 < q \le n$, `orderPrice` returns $f_i$ with $i$ the largest index $\le m$ such that $q \le Q_i$ (`Nat.findGreatest`); since $Q_1 = n \ge q$ and $Q_{m+1} = 0 < q$, this $i$ satisfies $Q_{i+1} < q \le Q_i$, which is the paper's case. $P$ is not specified for $q > n$ (the Lean value there is junk) and the policies never evaluate it there. No hypothesis on the fares is built in; the theorems assume them.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 957, §2.1, Eqs. (6), (7), (8), (9) and the display defining P(q)

import Mathlib

namespace RobustBooking.MultiFare

/-- Eq. (6): `Δ = m - ∑_{i=2}^{m} f_i / f_{i-1}`. -/
noncomputable def Delta (m : ℕ) (f : ℕ → ℝ) : ℝ :=
  (m : ℝ) - ∑ i ∈ Finset.Icc 2 m, f i / f (i - 1)

/-- Protection levels, Eq. (7): `θ_i = (n/Δ)(i - ∑_{j=1}^{i} f_{j+1}/f_j)` for
`i = 1, …, m - 1`, together with `θ_m = n` (p. 957) and `θ_0 = 0` (so that Eq. (8) at
`i = 1` agrees with Eq. (9)). Values at indices `i > m` are not used. -/
noncomputable def theta (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 0
  else if i < m then n / Delta m f * ((i : ℝ) - ∑ j ∈ Finset.Icc 1 i, f (j + 1) / f j)
  else n

/-- Protection-level controls, Eqs. (8)–(9): `Q_i = n - θ_{i-1}` for `i = 1, …, m + 1`,
so `Q_1 = n` and `Q_{m+1} = 0`. `Q_i` caps the total quantity accepted from the classes
`i, i+1, …, m` (the fares `≤ f_i`). The index `i = 0` is not used. -/
noncomputable def Q (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (i : ℕ) : ℝ :=
  n - theta m f n (i - 1)

/-- The order quantity control function (display after Eq. (9)), on `0 ≤ q ≤ n`:
`P(0) = 0` and `P(q) = f_i` for `Q_{i+1} < q ≤ Q_i`, `1 ≤ i ≤ m`. For `0 < q ≤ n` the
index `i` is the largest `i ≤ m` with `q ≤ Q_i` (it satisfies `Q_{i+1} < q ≤ Q_i`,
using `Q_1 = n` and `Q_{m+1} = 0`). `P` is not defined by the paper for `q > n`; the
policies below never evaluate it there. -/
noncomputable def orderPrice (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (q : ℝ) : ℝ :=
  if q = 0 then 0 else f (Nat.findGreatest (fun i => q ≤ Q m f n i) m)

end RobustBooking.MultiFare



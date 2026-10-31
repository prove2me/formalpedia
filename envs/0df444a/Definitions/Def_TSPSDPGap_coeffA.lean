-- Prove2me | Definitions.Def_TSPSDPGap_coeffA
-- name    : TSPSDPGap_coeffA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:27.573452+00:00
-- url     : https://prove2.me/theorems/7c164eea-bf90-4e20-8ada-bee330b29218
-- title:
--   Coefficients $a_i$ of the circulant matrix $A$
-- statement:
--   Let $g\ge2$ be even with $g\mid n$, $g<n$, and $d=n/2$. For $1\le i\le d$,
--   $$
--   a_i=\begin{cases}\dfrac1{n-g}\Bigl[2+\dfrac4g\displaystyle\sum_{j=1}^{g-1}(g-j)\cos\Bigl(\frac{\pi ij}{d}\Bigr)\Bigr], & i<d,\\[2ex]
--   \dfrac1{n-g}\Bigl[1+\dfrac2g\displaystyle\sum_{j=1}^{g-1}(g-j)\cos\Bigl(\frac{\pi ij}{d}\Bigr)\Bigr], & i=d.\end{cases}
--   $$
--   They are the weights of $A=\sum_{i=1}^d a_iC_i$ in the feasible solution (3).
--
--   **Formalization Note** Real division and $d=\lfloor n/2\rfloor$; the second branch is used for every $i\ge d$, but only $i=d$ occurs.
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, §4.1, p.15

import Mathlib

namespace TSPSDPGap

/-- **The coefficients `a_i` of the circulant matrix `A`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, §4.1, p.15: "We set
a_i = 1/(n−g) [2 + (4/g) Σ_{j=1}^{g−1} (g − j) cos(πij/d)], i < d;
a_i = 1/(n−g) [1 + (2/g) Σ_{j=1}^{g−1} (g − j) cos(πij/d)], i = d", where `d = n/2` (p.5).

**Formalization Note.** `coeffA g n i` is `a_i` for the parameters `g, n`; it is real-valued
with real division, `d = n/2` (natural-number division; `n` is even in the paper) and
`Σ_{j=1}^{g−1}` is the sum over `Finset.Ico 1 g`. The paper uses `a_i` only for
`1 ≤ i ≤ d`; the `else` branch is the printed `i = d` case (its value for `i > d` is never
used). -/
noncomputable def coeffA (g n i : ℕ) : ℝ :=
  if i < n / 2 then
    1 / ((n : ℝ) - g) * (2 + 4 / (g : ℝ) * ∑ j ∈ Finset.Ico 1 g,
      ((g : ℝ) - j) * Real.cos (Real.pi * i * j / (n / 2 : ℕ)))
  else
    1 / ((n : ℝ) - g) * (1 + 2 / (g : ℝ) * ∑ j ∈ Finset.Ico 1 g,
      ((g : ℝ) - j) * Real.cos (Real.pi * i * j / (n / 2 : ℕ)))

end TSPSDPGap



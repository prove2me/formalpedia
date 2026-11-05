-- Prove2me | Definitions.Def_BlindNRMLS_nu
-- name    : BlindNRMLS_nu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:58.134545+00:00
-- url     : https://prove2.me/theorems/44b0da05-4b36-4159-b574-ca776208a1c5
-- title:
--   Algorithm 2 (5), Theorems 3–4 — $\nu(s,d)$, the rate exponent, the grid $t_l$ and the two brackets
-- statement:
--   The number of learning epochs is $\nu(s,d)=\lfloor (s-d-1)/(K-1)\rfloor$, with $\lfloor x\rfloor=0$ for $x\le 0$. The rate exponent is $1/(2-2^{-\nu})$. The grid of Algorithm 2 is $t_0=0$ and
--   $$
--   t_l=\Big\lfloor K^{1-\frac{2-2^{-(l-1)}}{2-2^{-\nu}}}\,T^{\frac{2-2^{-(l-1)}}{2-2^{-\nu}}}\Big\rfloor,\qquad l\ge 1,
--   $$
--   so that $t_{\nu+1}=T$. The upper bracket of Theorem 3 and the lower bracket of Theorem 4 are
--   $$
--   \sqrt{n^3(d+1)\log[(d+1)KT]}\,K^{1-\frac{1}{2-2^{-\nu}}}\log T\cdot T^{\frac{1}{2-2^{-\nu}}},\qquad (d+1)^{-3}K^{-\frac32-\frac{1}{2-2^{-\nu}}}(\log T)^{-\frac52}\,T^{\frac{1}{2-2^{-\nu}}},
--   $$
--   and $(d+1)\log[(d+1)KT](\log T)^2$ is the cap on $n$ under which the upper bound is stated.
--
--   These are the quantities that the optimal rate is expressed in.
--
--   **Formalization Note** `nu` uses truncated subtraction and natural division, which is exactly the source's floor convention for $K\ge 2$.
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, Algorithm 2, display (5), p.15; floor convention, p.3; Theorem 3, p.18; Theorem 4, p.19

import Mathlib

namespace BlindNRMLS

/-- `ν(s,d) = ⌊(s - d - 1)/(K - 1)⌋`.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, Algorithm 2, p.15, with `⌊x⌋ = 0` for `x ≤ 0` (p.3).

**Formalization Note.** Truncated subtraction and natural division are exactly the page's
convention when `K ≥ 2`. -/
def nu (s d K : ℕ) : ℕ := (s - d - 1) / (K - 1)

/-- The rate exponent `1/(2 - 2^{-ν})`: Theorems 3 and 4, pp.18–19. -/
noncomputable def rateExp (ν : ℕ) : ℝ := 1 / (2 - (2 : ℝ) ^ (-(ν : ℝ)))

/-- The grid (5), p.15: `t_0 = 0` and
`t_l = ⌊K^{1 - (2-2^{-(l-1)})/(2-2^{-ν})} T^{(2-2^{-(l-1)})/(2-2^{-ν})}⌋` for `l ≥ 1`. -/
noncomputable def tSched (T K ν l : ℕ) : ℕ :=
  if l = 0 then 0
  else
    let e : ℝ := (2 - (2 : ℝ) ^ (-((l : ℝ) - 1))) / (2 - (2 : ℝ) ^ (-(ν : ℝ)))
    ⌊(K : ℝ) ^ (1 - e) * (T : ℝ) ^ e⌋₊

/-- The bracket of Theorem 3, p.18:
`√(n³(d+1) log[(d+1)KT]) K^{1 - 1/(2-2^{-ν})} log T · T^{1/(2-2^{-ν})}`. -/
noncomputable def upperBracket (T d K n ν : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) ^ 3 * ((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) * K * T)) *
    (K : ℝ) ^ (1 - rateExp ν) * Real.log T * (T : ℝ) ^ (rateExp ν)

/-- The bracket of Theorem 4, p.19:
`(d+1)^{-3} K^{-3/2 - 1/(2-2^{-ν})} (log T)^{-5/2} · T^{1/(2-2^{-ν})}`.

**Formalization Note.** Used only for `T ≥ 2`, where `log T > 0`; `0 ^ (-5/2) = 0` in Lean would make
the bound trivial at `T = 1`. -/
noncomputable def lowerBracket (T d K ν : ℕ) : ℝ :=
  ((d : ℝ) + 1) ^ (-3 : ℝ) * (K : ℝ) ^ (-(3 / 2 : ℝ) - rateExp ν) *
    Real.log T ^ (-(5 / 2 : ℝ)) * (T : ℝ) ^ (rateExp ν)

/-- The cap `(d+1) log[(d+1)KT] (log T)²` on the number of products, the correction of Theorem 3
for `n` growing with `T`. -/
noncomputable def nCap (T d K : ℕ) : ℝ :=
  ((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) * K * T) * Real.log T ^ 2

end BlindNRMLS



-- Prove2me | Definitions.Def_ThreeSumSharpTail_Analysis
-- name    : ThreeSumSharpTail_Analysis
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-13T14:52:23.845623+00:00
-- url     : https://prove2.me/theorems/b56d5cec-ddba-427e-af0b-de2c29aa207d
-- title:
--   Entropy, box counts, and cost exponents for the sharp-tail analysis
-- statement:
--   Defines $H(x)=-x\log x-(1-x)\log(1-x)$ (so $H(0)=H(1)=0$), the old preprocessing saving $\gamma(c,\theta)=\theta\log((c-1)/9)/\log4$, the sharp saving $\gamma_*(c,\theta)=[cH(1/c)-cH((1-\theta)/c)-\theta\log9]/\log4$, the query exponent $q(\theta)=[H(\theta)+\theta\log9]/\log4$, and the encoding exponent $A(c)=[c\log10-cH(1/c)/2-(c-1)\log3]/\log4$. For natural numbers $c,m,d$, defines $\beta_d=\binom{cm}{m-d}9^{cm-m+d}$; later lemmas restrict to $c>10$, $m\ge1$ and $d\le m$. These are auxiliary analytic quantities, not a replacement for the campaign's shared word-RAM or 3SUM definitions. Real logarithms and division are total in Lean; intended domains are supplied by theorem hypotheses.
-- source:
--   Yuxuan Xu, Deterministic Integer 3SUM in O(n^1.999017) Time via a Sharper Binomial-Tail Analysis (13 October 2026), Hexagon submission https://hexagonmath.org/submit/d57cba23-2d89-4bcb-8180-7c1bde7d14e3; Sections 2 and 3.

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ThreeSumSharpTail

noncomputable def entropy (x : ℝ) : ℝ :=
  -x * Real.log x - (1 - x) * Real.log (1 - x)

noncomputable def oldSaving (c θ : ℝ) : ℝ :=
  θ * Real.log ((c - 1) / 9) / Real.log 4

noncomputable def sharpSaving (c θ : ℝ) : ℝ :=
  (c * entropy (1 / c) - c * entropy ((1 - θ) / c) - θ * Real.log 9) / Real.log 4

noncomputable def queryExponent (θ : ℝ) : ℝ :=
  (entropy θ + θ * Real.log 9) / Real.log 4

noncomputable def encodingExponent (c : ℝ) : ℝ :=
  (c * Real.log 10 - c * entropy (1 / c) / 2 - (c - 1) * Real.log 3) / Real.log 4

def boxCount (c m d : ℕ) : ℕ :=
  Nat.choose (c * m) (m - d) * 9 ^ (c * m - m + d)

end ThreeSumSharpTail



-- Prove2me | Definitions.Def_EqualSubsetSum_Faster_Exponents
-- name    : EqualSubsetSum_Faster_Exponents
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:22:07.768372+00:00
-- url     : https://prove2.me/theorems/3b33d772-d9ce-432f-a994-9f1ba57d379b
-- title:
--   Base-two entropy H, the exponents f, C, T of Lemma 7.1 and Appendix B.5, and the constants c★, p₀, p₁, p₂
-- statement:
--   - $H(t)=-t\log_2 t-(1-t)\log_2(1-t)$ with $0\log_2 0=0$ (base-two binary entropy).
--   - $f(p)=H(p)+2(1-p)-\log_2 3$.
--   - $C(p)=\min_{0\le q\le(1-p)/2}\max\{H(p)+q,\ (1-p)[1-H(q/(1-p))]\}$, defined as the infimum of the values over the interval.
--   - With $u=1-p$: $T(p,q)=\max\{H(p)+q,\ u[1-H(q/u)],\ \ell_A/2,\ 1/2\}$ where $\ell_A=H(p)+p+q+uH(q/u)$ (eq. (44)).
--   - $c_\star=.7336065$, $p_0=.2015$, $p_1=.2239380256$, $p_2=.229$ (exact rationals).
--
--   **Formalization Note.** $H(t)$ is Mathlib's `Real.binEntropy t / Real.log 2`.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 13-14, §2.2; p. 44, Lemma 7.1; p. 53, eq. (44); p. 44 and p. 46, §7

import Mathlib

namespace EqualSubsetSum.Faster

/-! The base-two binary entropy, the exponent functions of Lemma 7.1 and Appendix B.5, and the
rational constants of §7 (pp. 44–46). -/

/-- Base-two binary entropy `H(t) = -t log₂ t - (1-t) log₂(1-t)`, with `0 log₂ 0 = 0`
(§2.2, p. 14). Mathlib's `Real.binEntropy` uses the natural logarithm. -/
noncomputable def H (t : ℝ) : ℝ := Real.binEntropy t / Real.log 2

/-- The exponent of the fully compatible procedure, `f(p) = H(p) + 2(1-p) - log₂ 3`. -/
noncomputable def fCompat (p : ℝ) : ℝ := H p + 2 * (1 - p) - Real.logb 2 3

/-- The quantity minimized in `C(p)`: `max{H(p) + q, (1-p)[1 - H(q/(1-p))]}`. -/
noncomputable def stepTwoObjective (p q : ℝ) : ℝ :=
  max (H p + q) ((1 - p) * (1 - H (q / (1 - p))))

/-- `C(p) = min_{0 ≤ q ≤ (1-p)/2} max{H(p) + q, (1-p)[1 - H(q/(1-p))]}` (Lemma 7.1), written as
the infimum of the values on the interval. -/
noncomputable def Cstep (p : ℝ) : ℝ :=
  sInf (stepTwoObjective p '' Set.Icc 0 ((1 - p) / 2))

/-- `T(p, q) = max{H(p) + q, u[1 - H(q/u)], ℓ_A/2, 1/2}` with `u = 1 - p` and
`ℓ_A = H(p) + p + q + u H(q/u)` (eq. (44); the right side of (40)). -/
noncomputable def Tstep (p q : ℝ) : ℝ :=
  max (max (H p + q) ((1 - p) * (1 - H (q / (1 - p)))))
    (max ((H p + p + q + (1 - p) * H (q / (1 - p))) / 2) (1 / 2))

/-- `c★ = .7336065`. -/
noncomputable def cStar : ℝ := 7336065 / 10 ^ 7

/-- `p₀ = .2015`. -/
noncomputable def p0 : ℝ := 2015 / 10 ^ 4

/-- `p₁ = .2239380256`. -/
noncomputable def p1 : ℝ := 2239380256 / 10 ^ 10

/-- `p₂ = .229`. -/
noncomputable def p2 : ℝ := 229 / 10 ^ 3

end EqualSubsetSum.Faster



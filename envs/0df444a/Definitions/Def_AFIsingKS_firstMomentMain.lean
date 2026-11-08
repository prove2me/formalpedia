-- Prove2me | Definitions.Def_AFIsingKS_firstMomentMain
-- name    : AFIsingKS_firstMomentMain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:13:43.795812+00:00
-- url     : https://prove2.me/theorems/421d7856-1259-49c2-a0d6-85501933d773
-- title:
--   The main term of the first moment of $Z_{G,<\varepsilon}(\beta)$
-- statement:
--   For $\beta\in\mathbb C$ with $dn$ even, the main term in the first-moment estimate of Lemma 3.5 is
--   $$\sqrt{\frac{1+e^\beta}{d(e^\beta-1)+2}}\cdot2^n\Big(\frac{1+e^\beta}{2}\Big)^{dn/2},$$
--   with the branch of the square root that is analytic on the complement of the negative real line.
--
--   **Formalization Note** The square root is the principal branch of the complex power $1/2$. The exponent $dn/2$ is a natural number, because every statement assumes $dn$ even.
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Lemma 3.5, p.13

import Mathlib

open Complex

namespace AFIsingKS

/-- The main term of the first moment in Lemma 3.5 (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.13):
`√((1 + e^β)/(d(e^β − 1) + 2)) · 2^n · ((1 + e^β)/2)^{dn/2}`.

**Formalization Note.** The square root is `Complex.cpow · (1/2)`, the principal branch, analytic off
the negative real line as the page specifies. The exponent `d * n / 2` is natural-number division; it
is exact because every statement assumes `Even (n * d)`. -/
noncomputable def firstMomentMain (d n : ℕ) (β : ℂ) : ℂ :=
  ((1 + Complex.exp β) / ((d : ℂ) * (Complex.exp β - 1) + 2)) ^ (1 / 2 : ℂ) *
    (2 : ℂ) ^ n * ((1 + Complex.exp β) / 2) ^ (d * n / 2)

end AFIsingKS



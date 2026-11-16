-- Prove2me | Definitions.Def_TightClock_Supplement_h1Quantile
-- name    : TightClock_Supplement_h1Quantile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:16:37.4609+00:00
-- url     : https://prove2.me/theorems/bfe0a540-d7a7-4a01-b999-3944feb46e81
-- title:
--   Quantile of $H_1$, (5.4)
-- statement:
--   $H_1$ is the law with density $h_1(z)=1/(\lambda_1 z)$ on $[a/\beta,b]$, where $\lambda_1=\log(\beta b/a)$. Its distribution function is $\log(\beta z/a)/\lambda_1$, so its $u$-quantile is
--
--   $$\frac a\beta\,e^{\lambda_1u}\qquad(u\in[0,1]).$$
--
--   A draw from $H_1$ is this quantile at a uniform $u$.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §5.1.3, (5.3)–(5.4), p.24 (PDF p.27)

import Mathlib

set_option autoImplicit false

namespace TightClock.Supplement

/-- The `u`-quantile of `H₁`, the law with density `h₁(z) = 1/(λ₁ z)` on `[a/β, b]`, (5.4): its
distribution function is `log(βz/a)/λ₁` with `λ₁ = log(βb/a)` (5.3), so the quantile is
`(a/β) e^{λ₁ u}`. A draw from `H₁` is `h1Quantile a β λ₁ u` for a uniform `u`. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §5.1.3,
(5.3)–(5.4), p.24 (PDF 27). -/
noncomputable def h1Quantile (a β lam1 u : ℝ) : ℝ :=
  a / β * Real.exp (lam1 * u)

end TightClock.Supplement



-- Prove2me | Definitions.Def_TightClock_Supplement_h2Quantile
-- name    : TightClock_Supplement_h2Quantile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:16:55.411447+00:00
-- url     : https://prove2.me/theorems/0c5f2b19-dace-4208-b4f6-cb170006afb8
-- title:
--   Quantile of $H_2(x)$, (5.4)
-- statement:
--   $H_2(x)$ is the law with density $h_{2,x}(z)=(x/z-1)/(\lambda_2z)$ on $[x/\beta,x]$, where $\lambda_2=\beta-1-\log\beta$. Its distribution function on $[x/\beta,x]$ is
--
--   $$G_x(z)=\frac{1}{\lambda_2}\Big(\beta-\frac xz-\log\frac{\beta z}{x}\Big),$$
--
--   and its $u$-quantile is the least $z\in[x/\beta,x]$ with $G_x(z)\ge u$. A draw from $H_2(x)$ is this quantile at a uniform $u$.
--
--   **Formalization Note** For $x>0$, $\beta>1$ and $u\in[0,1]$ the defining set contains $x$ and is bounded below, so the infimum is attained.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §5.1.3, (5.3)–(5.4), p.24 (PDF p.27)

import Mathlib

set_option autoImplicit false

namespace TightClock.Supplement

/-- The `u`-quantile of `H₂(x)`, the law with density `h_{2,x}(z) = (x/z − 1)/(λ₂ z)` on `[x/β, x]`,
(5.4): its distribution function is `(β − x/z − log(βz/x))/λ₂` on `[x/β, x]`, with
`λ₂ = β − 1 − log β` (5.3), and the quantile is the least `z ∈ [x/β, x]` at which it reaches `u`. A
draw from `H₂(x)` is `h2Quantile β λ₂ x u` for a uniform `u`. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §5.1.3, (5.3)–(5.4), p.24
(PDF 27).

**Formalization Note** For `x > 0`, `β > 1` and `u ∈ [0,1]` the set is nonempty (it contains `x`) and
bounded below, so the infimum is a genuine minimum. -/
noncomputable def h2Quantile (β lam2 x u : ℝ) : ℝ :=
  sInf {z : ℝ | z ∈ Set.Icc (x / β) x ∧ u * lam2 ≤ β - x / z - Real.log (β * z / x)}

end TightClock.Supplement



-- Prove2me | Definitions.Def_SecondBestBT_gftTermN
-- name    : SecondBestBT_gftTermN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:09.657224+00:00
-- url     : https://prove2.me/theorems/8140effe-876e-411a-b8dd-fa1559cfbf59
-- title:
--   Summand of $\mathrm{GFT}(x)$ on $\mathbb Z_{\ge0}^2$
-- statement:
--   For seller and buyer priors $f_S,f_B$ on $\mathbb Z_{\ge0}$ and an allocation $x$, the summand of the gains from trade at $(s,b)$ is $x(s,b)\,f_S(s)\,f_B(b)\,(b-s)$, so that $\mathrm{GFT}(x)=\sum_{(s,b)\in\mathbb Z_{\ge0}^2}x(s,b)f_S(s)f_B(b)(b-s)$ when the series converges.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), display on p.13; Theorem 4.10, p.15

import Mathlib

namespace SecondBestBT

/-- The summand `x(s, b) f_S(s) f_B(b) (b − s)` of the gains from trade `GFT(x)` on `Z²_{≥0}`
(Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Section 4.4, display on p.13,
and Theorem 4.10, p.15), indexed by `p = (s, b) ∈ ℕ × ℕ`.

**Formalization Note** For a buyer prior with infinite support, `GFT(x)` is the series
`∑' p, gftTermN f_S f_B x p`; theorems state its summability. -/
def gftTermN (fS fB : ℕ → ℝ) (x : ℕ → ℕ → ℝ) (p : ℕ × ℕ) : ℝ :=
  x p.1 p.2 * fS p.1 * fB p.2 * ((p.2 : ℝ) - p.1)

end SecondBestBT



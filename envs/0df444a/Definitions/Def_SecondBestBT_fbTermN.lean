-- Prove2me | Definitions.Def_SecondBestBT_fbTermN
-- name    : SecondBestBT_fbTermN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:09.733891+00:00
-- url     : https://prove2.me/theorems/807ee22c-9e7c-4dcd-a683-cfb6440081c0
-- title:
--   Summand of $\mathrm{FB}$ on $\mathbb Z_{\ge0}^2$
-- statement:
--   For priors $f_S,f_B$ on $\mathbb Z_{\ge0}$, the summand of the first-best gains from trade at $(s,b)$ is $f_S(s)f_B(b)(b-s)^+$. The buyer prior has finite first-best GFT exactly when this nonnegative family is summable.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), display on p.13

import Mathlib

namespace SecondBestBT

/-- The summand `f_S(s) f_B(b) (b − s)⁺` of the first-best gains from trade on `Z²_{≥0}`
(Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, display on p.13), indexed by
`p = (s, b)`. "Finite first-best GFT" is the summability of this nonnegative family. -/
def fbTermN (fS fB : ℕ → ℝ) (p : ℕ × ℕ) : ℝ :=
  fS p.1 * fB p.2 * max ((p.2 : ℝ) - p.1) 0

end SecondBestBT



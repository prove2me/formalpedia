-- Prove2me | Definitions.Def_ReusableMatching_fBound
-- name    : ReusableMatching_fBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:31:22.411709+00:00
-- url     : https://prove2.me/theorems/aef3c8c8-f3b5-48c7-a34b-83ca4c178b88
-- title:
--   The function $f(z_1,z_2,x)$ of the proof of Theorem 1
-- statement:
--   For $\beta>0$ define
--
--   $$
--   f(z_1,z_2,x)=G(z_2)-G(z_1)+(1-g(x))(1-z_1)+(1-z_2)\bigl(G(x)-G(0)\bigr)+z_1\bigl(1-g(0)\bigr).
--   $$
--
--   It is the bracket of the lower bound of Lemma 9, with $x=y^c_j(1)$; its minimum over $0\le z_1\le z_2\le1$, $x\in[0,1]$ is the competitive ratio the analysis certifies.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, proof of Theorem 1, p.13

import Mathlib
import Definitions.Def_ReusableMatching_G__bf4f7e

namespace ReusableMatching

/-- **The function `f(z1, z2, x)`** of the proof of Theorem 1 (arXiv:2110.07084v2, p.13): "Let
`f(z1, z2, x) = G(z2) − G(z1) + (1 − g(x))(1 − z1) + (1 − z2)(G(x) − G(0)) + z1(1 − g(0))`."
It is the bracket of the lower bound of Lemma 9 (p.11), with `x = y^c_j(1)`. -/
noncomputable def fBound (β z1 z2 x : ℝ) : ℝ :=
  G β z2 - G β z1 + (1 - g β x) * (1 - z1) + (1 - z2) * (G β x - G β 0) + z1 * (1 - g β 0)

end ReusableMatching



-- Prove2me | Definitions.Def_ReusableMatching_G__bf4f7e
-- name    : ReusableMatching_G
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:36.316191+00:00
-- url     : https://prove2.me/theorems/bf4f7e94-8f98-430b-9dff-eef381ae6ba9
-- title:
--   The antiderivative $G(x)=g(x)/\beta$
-- statement:
--   For $\beta\ne0$, the function
--
--   $$
--   G(x)=\frac{1}{\beta}\,e^{\beta(x-1)}
--   $$
--
--   is an antiderivative of $g(x)=e^{\beta(x-1)}$. Lemma 9 and the proof of Theorem 1 use only differences of $G$, so the choice of the additive constant does not matter.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, p.11 ("Let G(x) be the antiderivative of g(x)"), p.13 ("G(x) = (1/β) g(x) + c")

import Mathlib
import Definitions.Def_ReusableMatching_g

namespace ReusableMatching

/-- **The antiderivative `G` of `g`** (arXiv:2110.07084v2, p.11: "Let `g(x) = e^{β(x−1)}` for some
`β ∈ (0, 1]`. Let `G(x)` be the antiderivative of `g(x)`"; p.13: "`G(x) = (1/β) g(x) + c`, where
`c` is some constant").

**Formalization Note.** The constant is fixed to `c = 0`: `G(x) = g(x) / β`. Only differences of
`G` occur in Lemma 9 and in the proof of Theorem 1, so the choice of `c` changes nothing. -/
noncomputable def G (β x : ℝ) : ℝ :=
  g β x / β

end ReusableMatching



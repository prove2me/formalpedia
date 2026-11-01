-- Prove2me | Definitions.Def_SimpleMenus_CR
-- name    : SimpleMenus_CR
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:37:41.555792+00:00
-- url     : https://prove2.me/theorems/d6699394-ad09-4a9a-863f-006dc29163d3
-- title:
--   Competitive ratio $\mathrm{CR}(\pi)$
-- statement:
--   The competitive ratio of the $n$-level mechanism $\pi$ (price levels $v$, probabilities $x$) is its worst-case revenue relative to the clairvoyant benchmark over the ambiguity set:
--
--   $$\mathrm{CR}(\pi)=\inf_{F\in\mathcal F}\frac{\mathrm{Rev}(\pi,F)}{\mathrm{Rev}(\mathrm{OPT},F)}.$$
--
--   The seller's robust problem (1) maximizes this quantity over $\pi\in\Pi_n$.
--
--   **Formalization Note** The value lies in the extended reals. The infimum runs over the laws with $\mathrm{Rev}(\mathrm{OPT},F)>0$: a law with $\mathrm{Rev}(\mathrm{OPT},F)=0$ is a point mass at $0$, has zero revenue, and gives the ratio $0/0$; the proof's own constraint form (EC.1), $r\,p\,(1-F(p-))\le\mathrm{Rev}(\pi,F)$, places no restriction on it. The infimum is $+\infty$ when no law has a positive benchmark.
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, §2, p.9

import Mathlib
import Definitions.Def_SimpleMenus_pay
import Definitions.Def_SimpleMenus_rev
import Definitions.Def_SimpleMenus_opt
import Definitions.Def_SimpleMenus_ambiguitySet

open MeasureTheory Set

namespace SimpleMenus

/-- The competitive ratio `CR(π) = inf_{F ∈ 𝓕} Rev(π, F) / Rev(OPT, F)` of the `n`-level
mechanism with price levels `v` and probabilities `x` (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, §2, p.9).

Formalization Note: the value is in `EReal`. The infimum runs over the laws `F ∈ 𝓕` with
`Rev(OPT, F) > 0`. A law with `Rev(OPT, F) = 0` is carried by `{0}` and has `Rev(π, F) = 0`, so its
ratio is `0/0`; the proof's constraint form (EC.1), `r·p·(1 − F(p−)) ≤ Rev(π, F)`, places no
restriction on such laws. The infimum is `⊤` when no law has a positive benchmark. -/
noncomputable def CR (vbar : ℝ) {K n : ℕ} (phi : Fin K → ℝ → ℝ) (v x : Fin n → ℝ) : EReal :=
  ⨅ F ∈ ambiguitySet vbar phi, ⨅ (_ : 0 < opt vbar F),
    ((rev v x F : ℝ) : EReal) / ((opt vbar F : ℝ) : EReal)

end SimpleMenus



-- Prove2me | Definitions.Def_HDXHitting_Supplement_IsTwoSidedHDX
-- name    : HDXHitting_Supplement_IsTwoSidedHDX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:50:22.538487+00:00
-- url     : https://prove2.me/theorems/a71655b0-7abf-46d8-824d-ff0a443997dc
-- title:
--   $\lambda$-two-sided HDX
-- statement:
--   Let $X$ be a $d$-dimensional complex with top distribution $\pi_d$, and let $\lambda\ge0$. For a face $\tau$, the **link graph** $(X_\tau(1),X_\tau(2))$ has the vertices $u\notin\tau$ and edge weights $w_\tau(u,w)=\Pr_{\sigma\sim\pi_d}[\tau\cup\{u,w\}\subseteq\sigma]$ for $u\ne w$. The complex is a **$\lambda$-two-sided HDX** if for every face $\tau$ of codimension
--   $$
--   \operatorname{codim}\tau=d-|\tau|\ge2
--   $$
--   the random walk on the link graph of $\tau$ has second singular value at most $\lambda$: every nontrivial eigenvalue of the walk has absolute value at most $\lambda$. In Rayleigh form, with degrees $\deg_\tau(u)=\sum_w w_\tau(u,w)$, for all $g,h$ with $\sum_u\deg_\tau(u)g(u)=\sum_u\deg_\tau(u)h(u)=0$,
--   $$
--   \Big(\sum_{u,w}w_\tau(u,w)\,g(u)h(w)\Big)^2\le\lambda^2\Big(\sum_u\deg_\tau(u)g(u)^2\Big)\Big(\sum_u\deg_\tau(u)h(u)^2\Big).
--   $$
--
--   Two-sided expansion bounds both ends of the link spectra, while one-sided expansion bounds only the second largest eigenvalue; Theorem 4.1 gives its sharpest Chernoff bound under this hypothesis.
--
--   **Formalization Note** The condition is the published `HDXHitting.BipSingLE` applied to the published link weights `HDXHitting.linkWeight` on both sides; codimension $\ge2$ is `τ.card + 2 ≤ d`, including $\tau=\emptyset$, and the quantifier runs over all vertex sets (a non-face has zero weights, so the condition is empty there), exactly as in the published `HDXHitting.IsOneSidedHDX`. No connectivity, regularity or positive degree is assumed.
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d9400dc6e1b6e21e0efe05488a4e247d1be3b89a9c202e92f1e3e56d3), Definition 2.2, p.13

import Mathlib
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXHitting_BipSingLE

namespace HDXHitting.Supplement

open HDXHitting

/-- Definition 2.2 (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027
submission manuscript (sha256 60d23b0d…e56d3), p.13), two-sided part: a `d`-dimensional complex
with top distribution `p` is a **`λ`-two-sided HDX** if for every face `τ` of codimension
`codim τ = d − |τ| ≥ 2` the induced graph `(X_τ(1), X_τ(2))` of its link has second singular
value at most `λ`.

**Formalization Note** `codim τ ≥ 2` is `τ.card + 2 ≤ d` (dimension = number of vertices),
including `τ = ∅`, whose link is the complex itself; for a non-face all link weights vanish and
the condition holds trivially (same convention as the published `HDXHitting.IsOneSidedHDX`).
"Second singular value `≤ λ`" is the published Rayleigh-form predicate `HDXHitting.BipSingLE`
applied to the link graph on both sides: the link weights are symmetric, so the walk `D⁻¹W` is
self-adjoint on `L²(deg)` and maps the mean-zero functions to themselves, and its norm there is
its second singular value, the largest absolute value of a nontrivial eigenvalue. No
connectivity, regularity or positivity of weights is assumed. -/
def IsTwoSidedHDX {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (p : Finset V → ℝ)
    (lam : ℝ) : Prop :=
  ∀ τ : Finset V, τ.card + 2 ≤ d → BipSingLE (linkWeight p τ) lam

end HDXHitting.Supplement



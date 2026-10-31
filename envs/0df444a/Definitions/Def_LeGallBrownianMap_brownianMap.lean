-- Prove2me | Definitions.Def_LeGallBrownianMap_brownianMap
-- name    : LeGallBrownianMap_brownianMap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:52.02193+00:00
-- url     : https://prove2.me/theorems/da4a0360-b989-452f-b6fc-a68b7b9f4b98
-- title:
--   The Brownian map $(m_\infty, D^*)$
-- statement:
--   Let $e$ be a normalized Brownian excursion and $Z$ Brownian labels given $e$. On the CRT $\mathcal T_e$ put $a\simeq b$ iff $D^\circ(a,b)=0$; $\simeq$ is an equivalence relation, $m_\infty=\mathcal T_e/\!\simeq$, and
--
--   $$
--   D^*(x,y)=\inf\Big\{\sum_{i=1}^k D^\circ(a_{i-1},a_i)\Big\}
--   $$
--
--   (over chains with $\Pi(a_0)=x$, $\Pi(a_k)=y$) is a distance on $m_\infty$. The random compact metric space $(m_\infty, D^*)$ is the **Brownian map**. This definition gives its isometry class as a function of the paths $e$ and $Z$.
--
--   **Formalization Note** The space is $[0,1]/\{D^*=0\}$ with the distance induced by $D^*$ (`pseudoQuotientGH`). This is the paper's $\mathcal T_e/\!\simeq$ with $D^*$ because, almost surely, $D^*(a,b)=0$ iff $D^\circ(a,b)=0$ (p.15, from [15, Theorem 3.4]). For continuous paths $D^*$ is a pseudometric with compact quotient, so the junk value is never reached on the paper's objects.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §1, pp.3–4; §2.4, p.15

import Mathlib
import Definitions.Def_LeGallBrownianMap_dStar
import Definitions.Def_LeGallBrownianMap_pseudoQuotientGH

open GromovHausdorff

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §1,
pp.3–4: "we put a ≃ b if and only if D°(a, b) = 0. Although this is not obvious, it turns out
that ≃ is an equivalence relation on T_e, and we let m∞ := T_e/≃ be the associated quotient
space. […] We then define the distance on m∞ by setting […] D∗(x, y) = inf {…} (1) […] It follows
from [15], Theorem 3.4, that D∗ is indeed a distance, and the resulting random metric space
(m∞, D∗) is the Brownian map."

`brownianMap e Z` is the isometry class of `([0,1]/{D∗ = 0}, D∗)`, computed pathwise from an
excursion path `e` and a label path `Z`.

**Formalization Note.** The quotient is taken by `{D∗ = 0}` on `[0,1]` instead of by
`≃ = {D° = 0}` on `T_e`. The two agree: `D∗(s,t) = D∗(p_e(s), p_e(t))` (so `∼_e`-equivalent
times are identified), and "the property D∗(a, b) = 0 holds if and only if D°(a, b) = 0, for every
a, b ∈ T_e, a.s." (p.15, from [15], Theorem 3.4). So for almost every `(e, Z)` this is the
paper's `(m∞, D∗)`. `pseudoQuotientGH` returns `default` if `D∗` is not a pseudometric or the
quotient is not compact; neither happens for continuous `e`, `Z` (`D∗` is a chain infimum and
`D∗ ≤ D°`, which is continuous on `[0,1]²`). -/
noncomputable def brownianMap (e Z : unitInterval → ℝ) : GHSpace :=
  pseudoQuotientGH unitInterval (dStar e Z)

end LeGallBrownianMap



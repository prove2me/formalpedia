-- Prove2me | Definitions.Def_UnionVolEst_badSet
-- name    : UnionVolEst_badSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:02:41.934229+00:00
-- url     : https://prove2.me/theorems/cf60cc4d-1a47-46d1-b03f-7279d0f53b31
-- title:
--   Exceptional region $\mathrm{Bad}_\eta(D,\pi)=\{x:|h(x)-1|>\eta\}$ (Eq. (1))
-- statement:
--   Let $(S,\mathcal F,\pi)$ be a probability space and let $D$ be another probability distribution on $S$, absolutely continuous with respect to $\pi$, with relative density $h = \frac{dD}{d\pi}$. For $\eta \in (0,1)$ the **exceptional region** is
--   $$
--   \mathrm{Bad}_\eta(D,\pi) := \{x \in S : |h(x) - 1| > \eta\}.
--   $$
--   Outside this region the sampling distribution is multiplicatively close to $\pi$: $1-\eta \le h(x) \le 1+\eta$.
--
--   The region is the set on which an approximate sampler may deviate arbitrarily from the target; Definition 2 controls its mass under both distributions.
--
--   **Formalization Note** $h$ is the Radon–Nikodym derivative `D.rnDeriv π`, read as a real number (a point where the chosen representative equals $\infty$ reads as $0$ and lies in the region for every $\eta<1$). Under $D \ll \pi$ the measures of the region do not depend on the representative.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §3.1, Eq. (1), p.11 (PDF p.13)

import Mathlib

open MeasureTheory

namespace UnionVolEst

/-- The exceptional region of Eq. (1) (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §3.1, printed p.11, PDF p.13): for a probability
space `(S, F, π)`, a distribution `D` on `S` with relative density `h = dD/dπ` and `η ∈ (0, 1)`,
`Bad_η(D, π) := {x ∈ S : |h(x) − 1| > η}`.

**Formalization Note** The density `h` is Mathlib's Radon–Nikodym derivative `D.rnDeriv π`,
read in `ℝ` through `ENNReal.toReal` (a point where the chosen representative is `∞` reads as
`0` and is therefore in the region for every `η < 1`). When `D ≪ π` (bundled in
`IsAlmostLinftyClose`), `π` and `D` of the region do not depend on the representative. No
measure-theoretic assumption is bundled here; the range `η ∈ (0, 1)` is a hypothesis of the
results that use it. -/
noncomputable def badSet {S : Type*} [MeasurableSpace S] (η : ℝ) (D π : Measure S) : Set S :=
  {x | η < |(D.rnDeriv π x).toReal - 1|}

end UnionVolEst



-- Prove2me | Definitions.Def_ScarceIdeas_CostDensity
-- name    : ScarceIdeas_CostDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:02.959981+00:00
-- url     : https://prove2.me/theorems/330fdb13-1acf-4a35-a4e4-d3d329994c23
-- title:
--   Cost density $f$ on its support $[\underline c,\overline c]$
-- statement:
--   Ideas carry an R&D cost $c$ drawn independently from a fixed distribution. The **cost density** condition on $(\underline c,\overline c,f)$ says:
--
--   1. $0\le\underline c<\overline c$;
--   2. $f$ is continuous on $[\underline c,\overline c]$ and $f(c)>0$ there;
--   3. $f(c)=0$ for $c\notin[\underline c,\overline c]$, so $[\underline c,\overline c]$ is the support of $f$;
--   4. $\int_{\underline c}^{\overline c}f(c)\,dc=1$.
--
--   Every statement of the mission assumes it for the cost density.
--
--   **Formalization Note** The page's $\underline c$, $\overline c$ are `cL`, `cH`.
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, §2, p.9

import Mathlib

namespace ScarceIdeas

/-- **Cost density of ideas on its support `[c̲, c̄]`.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
§2, p.9: "We assume that the cost distribution is given by a continuous probability density f
with f > 0 on its support [c̲, c̄] in R+ and cumulative distribution F."

`CostDensity cL cH f` says that `f` is a probability density on `ℝ` whose support is the interval
`[cL, cH] ⊂ [0, ∞)` (the page's `c̲ < c̄`), that `f` is continuous and strictly positive on that
interval, and that it vanishes outside it.

**Formalization Note** The page's `c̲`, `c̄` are `cL`, `cH`. "Support `[c̲, c̄]`" is encoded as
`f = 0` off `[cL, cH]`; "probability density" as `∫_{cL}^{cH} f = 1` (with `f > 0` on the
interval, `f` is nonnegative everywhere). Continuity is required on the support, as the page's
"continuous … with f > 0 on its support" is about the density on its support. -/
def CostDensity (cL cH : ℝ) (f : ℝ → ℝ) : Prop :=
  0 ≤ cL ∧ cL < cH ∧ ContinuousOn f (Set.Icc cL cH) ∧ (∀ c ∈ Set.Icc cL cH, 0 < f c) ∧
    (∀ c, c ∉ Set.Icc cL cH → f c = 0) ∧ ∫ c in cL..cH, f c = 1

end ScarceIdeas



-- Prove2me | Definitions.Def_ScarceIdeas_IsAdmissible
-- name    : ScarceIdeas_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:05.593419+00:00
-- url     : https://prove2.me/theorems/bfe65904-58d4-4528-ad2d-e9dee4db5b14
-- title:
--   Admissible reward policy $p(t)\in[\underline c,\overline c]$
-- statement:
--   A reward policy is a function $u$ of calendar time $t\ge0$ giving the reward offered to the first innovator at time $t$. It is **admissible** when $u(t)\in[\underline c,\overline c]$ for all $t\ge0$ and $u$ is measurable on $(0,\infty)$.
--
--   **Formalization Note** The paper does not name a policy class; measurability makes every integral built from $u$ a genuine integral. Values at $t<0$ play no role.
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, §4.2, p.21

import Mathlib

namespace ScarceIdeas

/-- **Admissible reward policy.**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
§4.2, p.21: "In (17), we assume that p(t) ∈ [c̲, c̄], which is the support of the cost
distribution F."

An (open-loop) reward policy is a function `u` of calendar time `t ≥ 0` with values in the cost
support `[cL, cH]`, measurable on `(0, ∞)`.

**Formalization Note** The paper does not name a policy class; measurability (a.e. strong
measurability on `(0, ∞)`) is the reading that makes the cumulative incentive `∫_0^t F(p(s)) ds`
and the welfare integral genuine integrals. Values of `u` at `t < 0` play no role. -/
def IsAdmissible (cL cH : ℝ) (u : ℝ → ℝ) : Prop :=
  MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume.restrict (Set.Ioi 0)) ∧
    ∀ t, 0 ≤ t → u t ∈ Set.Icc cL cH

end ScarceIdeas



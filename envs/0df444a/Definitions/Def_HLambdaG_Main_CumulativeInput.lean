-- Prove2me | Definitions.Def_HLambdaG_Main_CumulativeInput
-- name    : HLambdaG_Main_CumulativeInput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:02:07.290016+00:00
-- url     : https://prove2.me/theorems/540ac913-e8a7-492d-8659-1f17fa551ea0
-- title:
--   §1, p. 635 — cumulative input F(s, t)
-- statement:
--   A **cumulative input** is a real-valued function $F$ on $[0,\infty)\times[0,\infty)$ that is nondecreasing in each coordinate. For each fixed $s$ and $t$, respectively, the marginal limits
--   $$
--   F(s,\infty)=\lim_{u\to\infty}F(s,u),\qquad
--   F(\infty,t)=\lim_{u\to\infty}F(u,t)
--   $$
--   are finite.
--
--   This is the general input object from which the paper forms its customer and time averages. It is useful for sample paths beyond ordinary queues.
--
--   **Formalization Note** The Lean structure uses nonnegative reals for both coordinates, real values for $F$, and bounded-above ranges for the finite marginal limits. It imposes neither $F\geq0$ nor the rectangle-increment inequality; the paper explicitly declines the latter.
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 635, §1; https://doi.org/10.1287/opre.37.4.634

import Mathlib

open scoped NNReal

namespace HLambdaG.Main

/-- The cumulative input of §1: separately nondecreasing with finite marginal limits. -/
structure CumulativeInput where
  F : ℝ≥0 → ℝ≥0 → ℝ
  mono_s : ∀ t, Monotone (fun s => F s t)
  mono_t : ∀ s, Monotone (F s)
  bdd_t : ∀ s, BddAbove (Set.range (F s))
  bdd_s : ∀ t, BddAbove (Set.range (fun s => F s t))

end HLambdaG.Main



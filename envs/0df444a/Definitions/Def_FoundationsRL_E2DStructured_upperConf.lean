-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_upperConf
-- name    : FoundationsRL_E2DStructured_upperConf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:02.285731+00:00
-- url     : https://prove2.me/theorems/84f41b2f-f0f9-405f-888f-712c334a3ae8
-- title:
--   The upper confidence function $\bar f^t$
-- statement:
--   The upper confidence function of a class $\mathcal F^t$ is
--   $$\bar f^t(\pi)=\max_{f\in\mathcal F^t}f(\pi).$$
--   The UCB strategy selects its maximizer.
--
--   **Formalization Note** The maximum is read as a real supremum; the statements using it assume the values bounded above.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.4.1, p. 76

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The upper confidence function `f̄^t(π) = max_{f∈F^t} f(π)` of a class
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.4.1, p. 76).

**Formalization Note.** `max` is read `sup`; every statement that uses it assumes the pointwise values
bounded above, so the real `sSup` is genuine. -/
noncomputable def upperConf {D : Type*} (G : Set (D → ℝ)) (π : D) : ℝ :=
  sSup ((fun f : D → ℝ => f π) '' G)

end FoundationsRL.E2DStructured



-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_IsUtilityFunction
-- name    : BauerleRiederMDP_RegimeSwitching_IsUtilityFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:54.437211+00:00
-- url     : https://prove2.me/theorems/c285ddde-f4fc-4b58-9d95-5c36c1d5e113
-- title:
--   Utility function on $\operatorname{dom} U$ (Definition 3.4.1)
-- statement:
--   A function $U:\operatorname{dom}U\to\mathbb R$ is a **utility function** if it is strictly increasing, strictly concave and continuous on $\operatorname{dom}U$.
--
--   For $\operatorname{dom}U=[0,\infty)$, continuity on $[0,\infty)$ includes right-continuity at $0$, which the book adds explicitly. This is the class of preferences of the consumption-investment problems of §4.3–§4.4, where $\operatorname{dom}U_c=\operatorname{dom}U_p=[0,\infty)$.
--
--   **Formalization Note** $U$ is a function on $\mathbb R$ and the three properties are required on the set $\operatorname{dom}U$ only; values outside it play no role.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 3.4.1, p.70 (PDF p.84), and p.71 (PDF p.85)

import Mathlib
open Set

namespace BauerleRiederMDP.RegimeSwitching

/-- **Utility function** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), Definition 3.4.1, p.70, PDF p.84): a function
`U : dom U → ℝ` is a utility function if it is strictly increasing, strictly concave and
continuous on `dom U`.

**Formalization Note.** `U` is a total function `ℝ → ℝ` and the three properties are required
on the set `dom`, so the values of `U` outside `dom` play no role. For `dom U = [0, ∞)` the book
adds (p.71) that `U` is right-continuous at `0`; `ContinuousOn U (Ici 0)` says exactly that
(continuity within `[0, ∞)`). -/
def IsUtilityFunction (U : ℝ → ℝ) (dom : Set ℝ) : Prop :=
  StrictMonoOn U dom ∧ StrictConcaveOn ℝ dom U ∧ ContinuousOn U dom

end BauerleRiederMDP.RegimeSwitching



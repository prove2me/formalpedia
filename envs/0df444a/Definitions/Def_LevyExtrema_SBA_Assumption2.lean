-- Prove2me | Definitions.Def_LevyExtrema_SBA_Assumption2
-- name    : LevyExtrema_SBA_Assumption2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:38:54.107048+00:00
-- url     : https://prove2.me/theorems/634d367f-602f-4eac-9106-7279bf3a48d6
-- title:
--   Assumption 2: $\mathbb P(X_t=x)=0$ for all $x\in\mathbb R$ and all $t>0$
-- statement:
--   A real-valued process $X=(X_t)_{t\ge0}$ on a probability space $(\Omega,\mathcal F,\mathbb P)$ satisfies **Assumption 2** if its marginals have no atoms:
--
--   $$\mathbb P(X_t=x)=0\quad\text{for all }x\in\mathbb R\text{ and all }t>0.$$
--
--   The paper states the assumption "for some (and hence all) $t>0$"; for a Lévy process the two forms are equivalent, and both are equivalent to $X$ not being compound Poisson with drift (milestone `not_cpp_tfae`). It is the standing assumption of Section 4 of the paper.
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, §4, Assumption 2, p. 17

import Mathlib

open MeasureTheory
open scoped NNReal

namespace LevyExtrema.SBA

/-- **Assumption 2 (atomless marginals).**
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, §4, p. 17: "Assumption 2.
P(X_t = x) = 0 for all x ∈ R and for some (and hence all) t > 0."

`Assumption2 P X := ∀ t > 0, ∀ x, P(X_t = x) = 0`.

**Formalization Note.** The "all t > 0" form is taken as the definition. That for a Lévy process
it is equivalent to the "some t > 0" form, and to the process not being compound Poisson with
drift, is the milestone `LevyExtrema.SBA.not_cpp_tfae`. -/
def Assumption2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ t : ℝ≥0, 0 < t → ∀ x : ℝ, P {ω | X t ω = x} = 0

end LevyExtrema.SBA



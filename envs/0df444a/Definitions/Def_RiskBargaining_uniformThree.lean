-- Prove2me | Definitions.Def_RiskBargaining_uniformThree
-- name    : RiskBargaining_uniformThree
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:24:24.00599+00:00
-- url     : https://prove2.me/theorems/557c65b4-ed78-4b05-994c-b7b40152cb6e
-- title:
--   The uniform probability measure on three points
-- statement:
--   The uniform probability measure on the set $\{1,2,3\}$, each point having mass $1/3$.
--
--   It is the probability space of the counterexample to Proposition 1.
--
--   **Formalization Note** The three points are the elements of `Fin 3`.
-- source:
--   Gutjahr, Kovacevic, Wozabal, Risk-Averse Bargaining in a Stochastic Optimization Context, manuscript, Appendix A.1, p.34 (the object is not in the paper)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace RiskBargaining

/-- **The uniform probability measure on the three-point space `Fin 3`.**
Used only by `RiskBargaining.proposition_1_counterexample`; Gutjahr, Kovacevic, Wozabal, *Risk-Averse Bargaining in a Stochastic Optimization Context*, manuscript, Appendix A.1, p.34, is the step that
the counterexample refutes. -/
noncomputable def uniformThree : Measure (Fin 3) :=
  (PMF.uniformOfFintype (Fin 3)).toMeasure

instance : IsProbabilityMeasure uniformThree := by
  unfold uniformThree
  infer_instance

end RiskBargaining



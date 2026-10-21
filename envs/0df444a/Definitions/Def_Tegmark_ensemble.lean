-- Prove2me | Definitions.Def_Tegmark_ensemble
-- name    : Tegmark_ensemble
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T04:10:53.148416+00:00
-- url     : https://prove2.me/theorems/1174a6e2-0861-41c9-bb1f-ee813913a850
-- title:
--   The ensemble layer: a probability space of worlds and the observer event
-- statement:
--   The ensemble layer of the letter. Ensemble theories — superstring theories with several stable or extremely long-lived compactifications, inflationary models with parts of exponentially large size of different dimensionality — predict not a single spacetime but a probability distribution over effective spacetime dimensionalities (page L69). A world ensemble is a measurable space of worlds with a probability measure, the effective numbers of space and of time dimensions of each world (the letter's n and m, the numbers of non-compactified dimensions, or more generally the effective dimensionalities relevant to the low-energy physics), and the measurable event of the worlds that contain observers. The layer carries only the measure-theoretic skeleton: the Bayesian selection arguments of the mission's goal theorem quantify over every world ensemble, with no assumption beyond the probability structure.
-- source:
--   M. Tegmark, On the dimensionality of spacetime, Class. Quantum Grav. 14 (1997) L69-L75, p. L69.

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys

namespace Tegmark

/-!
# On the dimensionality of spacetime: the ensemble layer

The ensemble layer of the letter: ensemble theories predict, not a
single spacetime, but a probability distribution over effective
spacetime dimensionalities (Tegmark 1997, p. L69). A world ensemble
is a probability space of worlds; each world carries its numbers of
space and time dimensions, and some worlds contain observers.
-/

/-- A world ensemble: a measurable space of worlds with a probability
measure, the effective numbers of space and time dimensions of each
world, and the measurable event of worlds containing observers
(Tegmark 1997, p. L69). -/
structure WorldEnsemble (W : Type) [MeasurableSpace W] where
  /-- the probability measure on the space of worlds -/
  μ : MeasureTheory.Measure W
  /-- the measure is a probability measure -/
  isProb : MeasureTheory.IsProbabilityMeasure μ
  /-- the effective number of space dimensions of each world -/
  nOf : W → ℕ
  /-- the effective number of time dimensions of each world -/
  mOf : W → ℕ
  /-- the worlds that contain observers -/
  hasObservers : Set W
  /-- the observer worlds form a measurable event -/
  obsMeasurable : MeasurableSet hasObservers

end Tegmark



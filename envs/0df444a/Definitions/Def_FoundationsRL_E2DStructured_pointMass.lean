-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_pointMass
-- name    : FoundationsRL_E2DStructured_pointMass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:58.99541+00:00
-- url     : https://prove2.me/theorems/5b1d779f-158c-495a-b271-a746de6c21f0
-- title:
--   The point mass at a decision
-- statement:
--   The point mass $\delta_\pi\in\Delta(\Pi)$ at a decision $\pi$ is the distribution of a deterministic strategy. The UCB strategy is the sequence of point masses at the maximizers of $\bar f^t$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.4.1, proof of Proposition 20, p. 76

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The point mass at a decision, the distribution of a deterministic strategy such as UCB
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.4.1, p. 76, proof of Proposition 20). -/
noncomputable def pointMass {D : Type*} [MeasurableSpace D] (π : D) : ProbabilityMeasure D :=
  ⟨Measure.dirac π, inferInstance⟩

end FoundationsRL.E2DStructured



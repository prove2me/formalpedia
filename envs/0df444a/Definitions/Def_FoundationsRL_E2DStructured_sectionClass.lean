-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_sectionClass
-- name    : FoundationsRL_E2DStructured_sectionClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:01.117984+00:00
-- url     : https://prove2.me/theorems/476f949e-ea47-4301-941b-427590a56e4e
-- title:
--   The projection $\mathcal F(x,\cdot)$ of a contextual class
-- statement:
--   For a class $\mathcal F$ of functions $f:\mathcal X\times\Pi\to\mathbb R$ and a context $x\in\mathcal X$, the projection onto $x$ is
--   $$\mathcal F(x,\cdot)=\{f(x,\cdot)\mid f\in\mathcal F\}.$$
--   It is the class of reward functions the learner faces once the context is revealed.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.5, p. 79

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The projection `F(x, ·) = {f(x, ·) | f ∈ F}` of a contextual class onto a context
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.5, p. 79). -/
def sectionClass {X D : Type*} (F : Set (X → D → ℝ)) (x : X) : Set (D → ℝ) :=
  (fun f : X → D → ℝ => f x) '' F

end FoundationsRL.E2DStructured



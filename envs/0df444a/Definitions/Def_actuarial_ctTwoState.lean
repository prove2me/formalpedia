-- Prove2me | Definitions.Def_actuarial_ctTwoState
-- name    : actuarial_ctTwoState
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:46:12.922083+00:00
-- url     : https://prove2.me/theorems/82622f9d-0f3c-4107-8372-76cd13b620a5
-- title:
--   Continuous two-status Markov survival and semigroup: ctTwoState
-- statement:
--   Alive–dead transition matrix with absorbing death, exact exponential survival. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Alive–dead transition matrix with absorbing death, exact} \\ \text{exponential survival.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 324. Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 19, sections 19.3–19.6, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Norberg and colleagues, Markov models and Thiele's integral equations for the prospective reserve (1997), https://doi.org/10.1016/S0167-6687(97)00020-6; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Finite actuarial multi-state generator conservation, continuous-time mortality transition matrices, and an analytically derived absorbing-state prospective reserve equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.sciencedirect.com/science/article/pii/S0167668797000206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctAlive
import Definitions.Def_actuarial_ctDead

namespace ActuarialValuation

noncomputable def ctTwoState (mu t : ℝ) (i j : Fin 2) : ℝ := if i=0 then (if j=0 then ctAlive mu t else ctDead mu t) else (if j=0 then 0 else 1)

end ActuarialValuation



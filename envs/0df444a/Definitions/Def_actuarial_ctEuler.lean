-- Prove2me | Definitions.Def_actuarial_ctEuler
-- name    : actuarial_ctEuler
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:44:46.247849+00:00
-- url     : https://prove2.me/theorems/de38b9a2-06e6-4699-b09c-93c5231200dc
-- title:
--   Conservative multi-state intensity matrices and forward Euler transition: ctEuler
-- statement:
--   Short-horizon forward-Euler transition matrix I+hQ. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{Short-horizon forward-Euler transition matrix I+hQ.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 324. Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 19, sections 19.3–19.6, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Norberg and colleagues, Markov models and Thiele's integral equations for the prospective reserve (1997), https://doi.org/10.1016/S0167-6687(97)00020-6; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Finite actuarial multi-state generator conservation, continuous-time mortality transition matrices, and an analytically derived absorbing-state prospective reserve equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.sciencedirect.com/science/article/pii/S0167668797000206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctGenerator

namespace ActuarialValuation

noncomputable def ctEuler (r : Fin 3 → Fin 3 → ℝ) (h : ℝ) (i j : Fin 3) : ℝ := (if i=j then 1 else 0)+h*ctGenerator r i j

end ActuarialValuation



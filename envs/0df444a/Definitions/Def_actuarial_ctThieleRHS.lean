-- Prove2me | Definitions.Def_actuarial_ctThieleRHS
-- name    : actuarial_ctThieleRHS
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:45:24.444083+00:00
-- url     : https://prove2.me/theorems/757a8b5d-cc52-49d6-8deb-a6f00ffad6bb
-- title:
--   Conservative multi-state intensity matrices and forward Euler transition: ctThieleRHS
-- statement:
--   Backward prospective-reserve Thiele RHS: discount less current outgo and generator action. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \begin{aligned}\text{Backward prospective-reserve Thiele RHS: discount less current} \\ \text{outgo and generator action.}\end{aligned}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 324. Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 19, sections 19.3–19.6, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Norberg and colleagues, Markov models and Thiele's integral equations for the prospective reserve (1997), https://doi.org/10.1016/S0167-6687(97)00020-6; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Finite actuarial multi-state generator conservation, continuous-time mortality transition matrices, and an analytically derived absorbing-state prospective reserve equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.sciencedirect.com/science/article/pii/S0167668797000206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ctBackward

namespace ActuarialValuation

noncomputable def ctThieleRHS (q : Fin 3 → Fin 3 → ℝ) (δ : ℝ) (b v : Fin 3 → ℝ) (i : Fin 3) : ℝ := δ*v i-b i-ctBackward q v i

end ActuarialValuation



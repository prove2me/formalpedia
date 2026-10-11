-- Prove2me | Definitions.Def_actuarial_ctTwoStep
-- name    : actuarial_ctTwoStep
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T15:46:22.012034+00:00
-- url     : https://prove2.me/theorems/7a935275-8817-48ff-a067-8c1799c1eab7
-- title:
--   Continuous two-status Markov survival and semigroup: ctTwoStep
-- statement:
--   Two-period transition composition in the CTMC model. The exact assumptions, units and boundary conventions are recorded separately in the formal statement.
--
--   Mathematical relation:
--
--   $$
--   \text{Two-period transition composition in the CTMC model.}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 324. Promislow (2015), Fundamentals of Actuarial Mathematics, Chapter 19, sections 19.3–19.6, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Norberg and colleagues, Markov models and Thiele's integral equations for the prospective reserve (1997), https://doi.org/10.1016/S0167-6687(97)00020-6; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Finite actuarial multi-state generator conservation, continuous-time mortality transition matrices, and an analytically derived absorbing-state prospective reserve equation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.sciencedirect.com/science/article/pii/S0167668797000206

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def ctTwoStep (A B : Fin 2 → Fin 2 → ℝ) (i k : Fin 2) : ℝ := ∑ j : Fin 2, A i j * B j k

end ActuarialValuation



-- Prove2me | Definitions.Def_actuarial_nhTransition
-- name    : actuarial_nhTransition
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:58:43.256926+00:00
-- url     : https://prove2.me/theorems/d5b15ec6-1a2e-417b-8243-910c0d9caf24
-- title:
--   Three-state transition probabilities and Chapman–Kolmogorov: nhTransition
-- statement:
--   Exact nonhomogeneous three-state transition probabilities. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   P_{00}(s,t)=e^{-(H(t)-H(s))},\quad P_{01}(s,t)=p(1-P_{00}(s,t))
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 30. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Frederik Møller and colleagues, Multi-state modeling in the mathematics of life insurance, https://www.math.ku.dk/bibliotek/arkivet/phd-theses/phd20cf.pdf; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Nonstationary linear hazard, competing exits, absorbing three-state transition laws and differentiable integral prospective reserves. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.math.ku.dk/bibliotek/arkivet/phd-theses/phd20cf.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhSurvival
import Definitions.Def_actuarial_nhExitOne
import Definitions.Def_actuarial_nhExitTwo

namespace ActuarialValuation

noncomputable def nhTransition (a b p s t : ℝ) (i j : Fin 3) : ℝ := if i=0 then (if j=0 then nhSurvival a b s t else if j=1 then nhExitOne a b p s t else nhExitTwo a b p s t) else (if i=j then 1 else 0)

end ActuarialValuation



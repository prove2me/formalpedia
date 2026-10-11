-- Prove2me | Definitions.Def_actuarial_nhCompose
-- name    : actuarial_nhCompose
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:58:50.741017+00:00
-- url     : https://prove2.me/theorems/b4400758-d881-4b5a-ae69-3de8ebfa96de
-- title:
--   Three-state transition probabilities and Chapman–Kolmogorov: nhCompose
-- statement:
--   Composition of transition kernels over adjacent periods. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

namespace ActuarialValuation

noncomputable def nhCompose (P Q : Fin 3 → Fin 3 → ℝ) (i k : Fin 3) : ℝ := ∑ j : Fin 3, P i j*Q j k

end ActuarialValuation



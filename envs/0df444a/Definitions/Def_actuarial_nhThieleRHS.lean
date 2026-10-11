-- Prove2me | Definitions.Def_actuarial_nhThieleRHS
-- name    : actuarial_nhThieleRHS
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:00:33.545021+00:00
-- url     : https://prove2.me/theorems/74fb91fc-d99f-4e5b-a23e-c3dd01a6384b
-- title:
--   Cause-contingent insurance and integral Thiele reserves: nhThieleRHS
-- statement:
--   Genuine competing-risk Thiele differential RHS with cause-specific exit payments. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   V'(t)=(\delta+\lambda(t))V(t)-\lambda(t)\bigl(pB_1+(1-p)B_2\bigr)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 30. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 19, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Frederik Møller and colleagues, Multi-state modeling in the mathematics of life insurance, https://www.math.ku.dk/bibliotek/arkivet/phd-theses/phd20cf.pdf; Buchardt, Møller and Schmidt (2015), https://doi.org/10.1080/03461238.2013.879919. Parent topic: Nonstationary linear hazard, competing exits, absorbing three-state transition laws and differentiable integral prospective reserves. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.math.ku.dk/bibliotek/arkivet/phd-theses/phd20cf.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhIntensity
import Definitions.Def_actuarial_nhCauseBenefit

namespace ActuarialValuation

noncomputable def nhThieleRHS (a b p δ B1 B2 t V : ℝ) : ℝ := (δ+nhIntensity a b t)*V-nhIntensity a b t*nhCauseBenefit p B1 B2

end ActuarialValuation



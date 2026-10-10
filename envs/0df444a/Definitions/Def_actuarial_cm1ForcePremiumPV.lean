-- Prove2me | Definitions.Def_actuarial_cm1ForcePremiumPV
-- name    : actuarial_cm1ForcePremiumPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T22:49:15.824067+00:00
-- url     : https://prove2.me/theorems/fe299da6-6b9e-42ae-9526-c7d237f0b07e
-- title:
--   Valuation of continuous benefits: cm1ForcePremiumPV
-- statement:
--   Expected present value of continuous premium income while the insured remains alive during the term. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   PV_P=P\frac{1-e^{-(\delta+\mu)T}}{\delta+\mu}
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2020), Policy Values, Chapter 7, printed page 250, Thiele's differential equation. Encyclopedia of Mathematics, Thiele differential equation, https://encyclopediaofmath.org/wiki/Thiele_differential_equation; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2020), Policy values and Thiele, https://www.kriso.ee/actuarial-mathematics-life-contingent-risks-3rd-db-9781108478083.html; Oxford Mathematics actuarial reserves and Thiele lecture, https://www.stats.ox.ac.uk/~winkel/bs4b11.pdf. Parent topic: Continuous force of interest and mortality, constant-force prospective reserves, Thiele's differential equation and terminal condition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Additional IFoA source syllabus: https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1ForceTermFactor

namespace ActuarialValuation

noncomputable def cm1ForcePremiumPV (δ μ premium T : ℝ) : ℝ := premium*cm1ForceTermFactor δ μ T 0

end ActuarialValuation



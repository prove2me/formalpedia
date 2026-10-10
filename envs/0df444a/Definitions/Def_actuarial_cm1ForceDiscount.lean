-- Prove2me | Definitions.Def_actuarial_cm1ForceDiscount
-- name    : actuarial_cm1ForceDiscount
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T22:45:25.415977+00:00
-- url     : https://prove2.me/theorems/65779709-a25d-4122-a848-5cd288a7e23d
-- title:
--   Continuous survival and discount: cm1ForceDiscount
-- statement:
--   Discount factor over t years under constant force of interest δ. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   v(t)=e^{-\delta t}
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2020), Policy Values, Chapter 7, printed page 250, Thiele's differential equation. Encyclopedia of Mathematics, Thiele differential equation, https://encyclopediaofmath.org/wiki/Thiele_differential_equation; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2020), Policy values and Thiele, https://www.kriso.ee/actuarial-mathematics-life-contingent-risks-3rd-db-9781108478083.html; Oxford Mathematics actuarial reserves and Thiele lecture, https://www.stats.ox.ac.uk/~winkel/bs4b11.pdf. Parent topic: Continuous force of interest and mortality, constant-force prospective reserves, Thiele's differential equation and terminal condition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Additional IFoA source syllabus: https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ActuarialValuation

noncomputable def cm1ForceDiscount (δ t : ℝ) : ℝ := Real.exp (-δ*t)

end ActuarialValuation



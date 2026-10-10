-- Prove2me | Definitions.Def_actuarial_cm1NominalInterest
-- name    : actuarial_cm1NominalInterest
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T21:30:13.638775+00:00
-- url     : https://prove2.me/theorems/ab1d9ad6-a374-43c2-b18c-b9dd110beb6b
-- title:
--   Interest rate algebra: cm1NominalInterest
-- statement:
--   A nominal rate from a given effective periodic rate j and a positive number of periods per annum. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   j^{(m)}=m j
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 2. Institute and Faculty of Actuaries, CM1 2026 syllabus, Sections 1–2, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; CM1_new_formula.pdf (user study notes), pages 1–4; standard actuarial financial mathematics and Redington local immunisation. Parent topic: CM1 financial mathematics: compound rates, annuity-certain, loan amortisation, bond discounting, duration, convexity and local Redington immunisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ActuarialValuation

noncomputable def cm1NominalInterest (j : ℝ) (m : ℝ) : ℝ := m * j

end ActuarialValuation



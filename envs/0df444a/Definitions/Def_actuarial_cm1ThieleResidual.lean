-- Prove2me | Definitions.Def_actuarial_cm1ThieleResidual
-- name    : actuarial_cm1ThieleResidual
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T22:48:14.437616+00:00
-- url     : https://prove2.me/theorems/c678a559-6a44-4b4a-869e-562f3389e804
-- title:
--   Insurance net outgo and prospective reserves: cm1ThieleResidual
-- statement:
--   Residual of the prospective reserve against the exact Thiele insurance ODE. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   E(t)=V'(t)-P-\delta V(t)+\mu(B-V(t))
--   $$
-- source:
--   Original derived result. Dickson, Hardy and Waters (2020), Policy Values, Chapter 7, printed page 250, Thiele's differential equation. Encyclopedia of Mathematics, Thiele differential equation, https://encyclopediaofmath.org/wiki/Thiele_differential_equation; Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2020), Policy values and Thiele, https://www.kriso.ee/actuarial-mathematics-life-contingent-risks-3rd-db-9781108478083.html; Oxford Mathematics actuarial reserves and Thiele lecture, https://www.stats.ox.ac.uk/~winkel/bs4b11.pdf. Parent topic: Continuous force of interest and mortality, constant-force prospective reserves, Thiele's differential equation and terminal condition. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Additional IFoA source syllabus: https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_actuarial_cm1ThieleReserve
import Definitions.Def_actuarial_cm1ThieleRHS

namespace ActuarialValuation

noncomputable def cm1ThieleResidual (δ μ benefit premium T t : ℝ) : ℝ := deriv (cm1ThieleReserve δ μ benefit premium T) t - cm1ThieleRHS δ μ benefit premium (cm1ThieleReserve δ μ benefit premium T t)

end ActuarialValuation



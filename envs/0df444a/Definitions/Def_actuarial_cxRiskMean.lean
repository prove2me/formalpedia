-- Prove2me | Definitions.Def_actuarial_cxRiskMean
-- name    : actuarial_cxRiskMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:59:55.469031+00:00
-- url     : https://prove2.me/theorems/53e52988-2bd1-4762-a513-352aa3335ad4
-- title:
--   Log-partial likelihood, weighted risk scores and inference: cxRiskMean
-- statement:
--   Risk-weighted covariate mean at a failure instant. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   U(\beta)=\sum_{i\in D}\left(z_i-\frac{\sum_{j\in R_i}z_je^{\beta z_j}}{\sum_{j\in R_i}e^{\beta z_j}}\right)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 190. D. R. Cox (1972), Regression Models and Life-Tables, Journal of the Royal Statistical Society B 34:187–202, https://doi.org/10.1111/j.2517-6161.1972.tb00899.x; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, lifetime failure-time models. Parent topic: Multiplicative baseline hazard, finite at-risk sets, partial likelihood, censored selection, score derivatives and survival prediction. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1111/j.2517-6161.1972.tb00899.x

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxRiskDenom
import Definitions.Def_actuarial_cxRiskWeighted

namespace ActuarialValuation

noncomputable def cxRiskMean {n : ℕ} (beta : ℝ) (risk : Finset (Fin n)) (z : Fin n → ℝ) : ℝ := cxRiskWeighted beta risk z/cxRiskDenom beta risk z

end ActuarialValuation



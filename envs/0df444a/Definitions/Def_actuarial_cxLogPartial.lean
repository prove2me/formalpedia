-- Prove2me | Definitions.Def_actuarial_cxLogPartial
-- name    : actuarial_cxLogPartial
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:00:30.780982+00:00
-- url     : https://prove2.me/theorems/21b1ab39-c633-4b01-bc93-c5f5d68ff895
-- title:
--   Log-partial likelihood, weighted risk scores and inference: cxLogPartial
-- statement:
--   Logarithmic Cox partial likelihood written without requiring a specified baseline hazard. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

namespace ActuarialValuation

noncomputable def cxLogPartial {n : ℕ} (beta : ℝ) (events : Finset (Fin n)) (risks : Fin n → Finset (Fin n)) (z : Fin n → ℝ) : ℝ := ∑ i ∈ events, (beta*z i-Real.log (cxRiskDenom beta (risks i) z))

end ActuarialValuation



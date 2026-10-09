-- Prove2me | Definitions.Def_actuarial_compoundPoissonCountWeight
-- name    : actuarial_compoundPoissonCountWeight
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T10:24:46.872975+00:00
-- url     : https://prove2.me/theorems/1f7070c6-55c0-494e-97b5-bd7afd4ef640
-- title:
--   Poisson claim-count probability coefficient
-- statement:
--   The count mass for exactly m claims has the conventional Poisson form: exponential zero-count probability multiplied by rate to the m power and divided by factorial m. The formula is real algebra, with the probabilistic interpretation requiring a nonnegative frequency parameter.
--
--   **Mathematical statement**
--
--   $$
--   p_m=e^{-\lambda}\lambda^m/m!
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib

namespace ActuarialValuation

noncomputable def compoundPoissonCountWeight (rate : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-rate) * rate ^ m / (Nat.factorial m : ℝ)

end ActuarialValuation



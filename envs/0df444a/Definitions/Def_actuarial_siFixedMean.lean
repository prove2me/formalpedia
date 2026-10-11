-- Prove2me | Definitions.Def_actuarial_siFixedMean
-- name    : actuarial_siFixedMean
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:59:56.33611+00:00
-- url     : https://prove2.me/theorems/9d504bd1-ffc6-41a5-a187-a41c4cf20f27
-- title:
--   Finite-scenario investment returns and fixed random rates: siFixedMean
-- statement:
--   Expected accumulation under a fixed-but-uncertain rate. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   S_n=(1+I)^n,\quad \mathbb{E}[S_n]=\sum_{\omega}p_{\omega}(1+I_{\omega})^n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 13. S. David Promislow, Fundamentals of Actuarial Mathematics (2015), Chapters on stochastic rates and annuity accumulation; Shreve (2004), Stochastic Calculus for Finance I, Chapter 1, https://link.springer.com/book/10.1007/978-0-387-22527-2. Parent topic: Finite-scenario expectation and variance; fixed random rate versus independent annual rates, product sample space and fund contribution moments. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://link.springer.com/book/10.1007/978-0-387-22527-2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siFixedAccum
import Definitions.Def_actuarial_siMean

namespace ActuarialValuation

noncomputable def siFixedMean {m : ℕ} (p : Fin m → ℝ) (r : Fin m → ℝ) (years : ℕ) : ℝ := siMean p (fun j => siFixedAccum (r j) years)

end ActuarialValuation



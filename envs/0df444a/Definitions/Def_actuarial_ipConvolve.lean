-- Prove2me | Definitions.Def_actuarial_ipConvolve
-- name    : actuarial_ipConvolve
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:57:07.160429+00:00
-- url     : https://prove2.me/theorems/358b3d00-bc5e-4cf1-b633-a02e4d0eca17
-- title:
--   Countably infinite count laws and convolution powers: ipConvolve
-- statement:
--   Genuine claim severity convolution at fixed k. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   p_n^{\mathrm{Poi}}=e^{-\lambda}\frac{\lambda^n}{n!}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results, https://doi.org/10.1017/S0515036100006802; Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 21. Parent topic: Poisson and geometric count laws, infinite frequency-severity convolution, analytic probability generating functions and corrected aggregate recursions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/abstract/recursive-evaluation-family-compound-distributions

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def ipConvolve (f g : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range (k+1), f j*g (k-j)

end ActuarialValuation



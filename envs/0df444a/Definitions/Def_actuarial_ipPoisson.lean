-- Prove2me | Definitions.Def_actuarial_ipPoisson
-- name    : actuarial_ipPoisson
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:57:34.940751+00:00
-- url     : https://prove2.me/theorems/2af47c71-1ad6-4e44-a030-91b5c7b9cccb
-- title:
--   Countably infinite count laws and convolution powers: ipPoisson
-- statement:
--   True infinite Poisson mass function. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

noncomputable def ipPoisson (l : ℝ) (n : ℕ) : ℝ := Real.exp (-l)*l^n/(Nat.factorial n : ℝ)

end ActuarialValuation



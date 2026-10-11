-- Prove2me | Definitions.Def_actuarial_ipGeoRHS
-- name    : actuarial_ipGeoRHS
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:59:09.958775+00:00
-- url     : https://prove2.me/theorems/f578d1ef-3d77-4406-b747-34f9d1d4872a
-- title:
--   Full Poisson and geometric infinite Panjer recurrence: ipGeoRHS
-- statement:
--   Geometric Panjer positive-amount RHS. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   (1-qf_0)g_k=q\sum_{j=1}^kf_jg_{k-j}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results, https://doi.org/10.1017/S0515036100006802; Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 21. Parent topic: Poisson and geometric count laws, infinite frequency-severity convolution, analytic probability generating functions and corrected aggregate recursions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/abstract/recursive-evaluation-family-compound-distributions

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def ipGeoRHS (q : ℝ) (f g : ℕ → ℝ) (k : ℕ) : ℝ := q*(∑ j ∈ Finset.range k, f (j+1)*g (k-(j+1)))

end ActuarialValuation



-- Prove2me | Definitions.Def_actuarial_ipCountPGF
-- name    : actuarial_ipCountPGF
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:58:19.152978+00:00
-- url     : https://prove2.me/theorems/9f42f9d4-9a7d-4557-9c78-d3e5caf257be
-- title:
--   Probability generating functions, mass normalisation and zero atoms: ipCountPGF
-- statement:
--   Infinite count probability generating series. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   g_k=\sum_{n=0}^{\infty}p_n(f^{*n})_k,\quad g_0=G_N(f_0)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 22. Harry H. Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, https://doi.org/10.1017/S0515036100006796; Sundt and Jewell (1981), Further Results, https://doi.org/10.1017/S0515036100006802; Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 21. Parent topic: Poisson and geometric count laws, infinite frequency-severity convolution, analytic probability generating functions and corrected aggregate recursions. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/abstract/recursive-evaluation-family-compound-distributions

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ActuarialValuation

noncomputable def ipCountPGF (p : ℕ → ℝ) (z : ℝ) : ℝ := ∑' n : ℕ, p n*z^n

end ActuarialValuation



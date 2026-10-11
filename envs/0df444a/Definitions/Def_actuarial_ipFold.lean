-- Prove2me | Definitions.Def_actuarial_ipFold
-- name    : actuarial_ipFold
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:57:26.237688+00:00
-- url     : https://prove2.me/theorems/95df38b5-a0ba-4d1b-95c4-251f6479e6bd
-- title:
--   Countably infinite count laws and convolution powers: ipFold
-- statement:
--   n-fold severity convolution for iid count n. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_ipPoint
import Definitions.Def_actuarial_ipConvolve

namespace ActuarialValuation

noncomputable def ipFold (f : ℕ → ℝ) (n : ℕ) : ℕ → ℝ := Nat.rec ipPoint (fun _ prev k => ipConvolve f prev k) n

end ActuarialValuation



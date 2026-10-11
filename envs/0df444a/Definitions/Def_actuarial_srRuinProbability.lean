-- Prove2me | Definitions.Def_actuarial_srRuinProbability
-- name    : actuarial_srRuinProbability
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:01:35.367256+00:00
-- url     : https://prove2.me/theorems/83e9486c-1000-4da2-90fc-f2b0a729599c
-- title:
--   Probability of ruin, monotonicity and severity overshoot: srRuinProbability
-- statement:
--   Actual measure of the union of stochastic first-passage events. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \psi_N(u)=\mathbb{P}(\min_{n\le N}U_n<0)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Hanspeter Schmidli, Risk Theory (2017), https://link.springer.com/book/10.1007/978-3-319-72005-0; probability ruin bound overview https://www.mdpi.com/2227-9091/12/2/28. Parent topic: Actual compound-Poisson embedded arrival paths, measurable first ruin events, disjoint first-hit times, deficit and conditional stopped-exponential Lundberg bound. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.mdpi.com/2227-9091/12/2/28

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srEverRuin

namespace ActuarialValuation

noncomputable def srRuinProbability {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (u c : ℝ) (W Y : ℕ → Ω → ℝ) : ℝ := (μ {ω | srEverRuin u c W Y ω}).toReal

end ActuarialValuation



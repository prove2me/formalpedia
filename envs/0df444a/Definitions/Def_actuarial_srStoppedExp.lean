-- Prove2me | Definitions.Def_actuarial_srStoppedExp
-- name    : actuarial_srStoppedExp
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T18:02:57.524416+00:00
-- url     : https://prove2.me/theorems/deb41e3b-ce9b-4a61-b576-199249daf39b
-- title:
--   Stopped exponential-loss process and conditional Lundberg capital bound: srStoppedExp
-- statement:
--   Stopped exponential loss process at the first ruin or bounded horizon. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \mathbb{E}[M_{\tau\wedge N}]\le1\ \Longrightarrow\ \psi_N(u)\le e^{-Ru}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Hanspeter Schmidli, Risk Theory (2017), https://link.springer.com/book/10.1007/978-3-319-72005-0; probability ruin bound overview https://www.mdpi.com/2227-9091/12/2/28. Parent topic: Actual compound-Poisson embedded arrival paths, measurable first ruin events, disjoint first-hit times, deficit and conditional stopped-exponential Lundberg bound. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.mdpi.com/2227-9091/12/2/28

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srRuinBy
import Definitions.Def_actuarial_srFirstHit
import Definitions.Def_actuarial_srExpLoss

namespace ActuarialValuation

noncomputable def srStoppedExp {Ω : Type*} (R u c : ℝ) (W Y : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ := by classical exact ((∑ n ∈ Finset.range (N+1), if srFirstHit u c W Y n ω then srExpLoss R c W Y n ω else 0)+(if srRuinBy u c W Y N ω then 0 else srExpLoss R c W Y N ω))

end ActuarialValuation



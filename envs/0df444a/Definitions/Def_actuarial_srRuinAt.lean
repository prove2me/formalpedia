-- Prove2me | Definitions.Def_actuarial_srRuinAt
-- name    : actuarial_srRuinAt
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:58:50.395236+00:00
-- url     : https://prove2.me/theorems/c25a8030-5b93-4f00-ac31-87d66e60e94d
-- title:
--   Embedded Poisson-arrival capital paths and first-passage partition: srRuinAt
-- statement:
--   Strict ruin at an actual claim-arrival boundary. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   U_n=u+c\sum_{j<n}W_j-\sum_{j<n}Y_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 3. S. David Promislow (2015), Fundamentals of Actuarial Mathematics, chapter 23, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; Hanspeter Schmidli, Risk Theory (2017), https://link.springer.com/book/10.1007/978-3-319-72005-0; probability ruin bound overview https://www.mdpi.com/2227-9091/12/2/28. Parent topic: Actual compound-Poisson embedded arrival paths, measurable first ruin events, disjoint first-hit times, deficit and conditional stopped-exponential Lundberg bound. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.mdpi.com/2227-9091/12/2/28

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srSurplus

namespace ActuarialValuation

def srRuinAt {Ω : Type*} (u c : ℝ) (W Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Prop := srSurplus u c W Y n ω<0

end ActuarialValuation



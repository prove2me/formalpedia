-- Prove2me | Definitions.Def_actuarial_c_premiumPath
-- name    : actuarial_c_premiumPath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:34:31.975494+00:00
-- url     : https://prove2.me/theorems/6f7c5726-8e92-43ed-b753-4ad5e58a8808
-- title:
--   Actual advance premium instalments until death or term expiry
-- statement:
--   Actual advance premium instalments until death or term expiry.
--
--   Mathematical relation:
--
--   $$
--   Y_n(k)=\sum_{j=0}^{n-1}v^j\mathbf{1}_{\{k\ge j\}}
--   $$
--
--   This is a separate actuarial cashflow definition, with units of money or present-value factors as determined by its parameters. Timing and endpoint conventions follow the event-level policy-year model.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.2, net premium ratio and premium stream, printed p. 63. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive

namespace ActuarialAssurances

noncomputable def premiumPath (n : ℕ) (v : ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range n, v^j*alive k j
end ActuarialAssurances



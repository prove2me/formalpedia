-- Prove2me | Definitions.Def_actuarial_c_massCohort
-- name    : actuarial_c_massCohort
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-12T19:50:41.631243+00:00
-- url     : https://prove2.me/theorems/73419122-ef18-471d-af78-c1b66f85332e
-- title:
--   Public-commutation-compatible survival cohort built from mortality state masses
-- statement:
--   Public-commutation-compatible survival cohort built from mortality state masses.
--
--   Mathematical relation:
--
--   $$
--   l_j=S(j)=\sum_{k=j}^{h}p_k
--   $$
--
--   This is a separate actuarial cashflow definition, with units of money or present-value factors as determined by its parameters. Timing and endpoint conventions follow the event-level policy-year model.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.7, general identity and actuarial notation, printed p. 71. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_surv

namespace ActuarialAssurances

noncomputable def massCohort (h : ℕ) (p : ℕ → ℝ) (j : ℕ) : ℝ := surv h p j
end ActuarialAssurances



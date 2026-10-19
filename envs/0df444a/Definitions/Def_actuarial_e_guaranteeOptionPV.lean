-- Prove2me | Definitions.Def_actuarial_e_guaranteeOptionPV
-- name    : actuarial_e_guaranteeOptionPV
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-16T17:43:20.064214+00:00
-- url     : https://prove2.me/theorems/a7243d45-1fa6-4534-84db-2a3739e7e808
-- title:
--   Scheme-elected estate guarantee stream or capital
-- statement:
--   Scheme-elected estate guarantee stream or capital. The Boolean contractual option selects one payable benefit form and prevents cumulative estate guarantee plus commuted capital.
--
--   The contractual and mortality relation is:
--
--   $$
--   G_{\text{option}}(\kappa)=\begin{cases}G_{\text{capital}},&\kappa=1\\G_{\text{stream}},&\kappa=0\end{cases}
--   $$
--
--   The object is defined at its stated payment dates. Amounts are per instalment or in pounds as appropriate; probabilities are dimensionless and discounts are to valuation.
-- source:
--   Originally derived finite-grid pension contract statement, based on the actuarial context in Chapter 10, p. 388, of Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, 3rd ed, Chapters 8–11. https://doi.org/10.1017/9781108784184 Specific benefit switches and endpoint rules are explicit new scheme assumptions, not verbatim textbook results.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_onlyY
import Definitions.Def_actuarial_d_mass
import Definitions.Def_actuarial_d_valid
import Definitions.Def_actuarial_d_expect
import Definitions.Def_actuarial_d_alive
import Definitions.Def_actuarial_e_guaranteeStreamPV
import Definitions.Def_actuarial_e_guaranteeCapitalPV

namespace ActuarialDeathE
noncomputable def guaranteeOptionPV (n h r g i : ℕ) (disc : ℕ → ℝ) (forward : ℕ → ℕ → ℝ) (base : ℕ → ℝ) (commute : Bool) : ℝ := if commute then guaranteeCapitalPV n h r g i disc forward base else guaranteeStreamPV n h r g i disc base
end ActuarialDeathE



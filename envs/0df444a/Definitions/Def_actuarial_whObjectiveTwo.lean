-- Prove2me | Definitions.Def_actuarial_whObjectiveTwo
-- name    : actuarial_whObjectiveTwo
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:13:24.761114+00:00
-- url     : https://prove2.me/theorems/662b516f-07f0-4fb9-9516-aa945453dd1d
-- title:
--   Composite graduation objective and invariance: whObjectiveTwo
-- statement:
--   Second-order graduation objective balances crude fit and smoothness of age trends. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   J_2=F+\lambda S_2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def whObjectiveTwo (fit smoothness lambda : ℝ) : ℝ := fit + lambda*smoothness

end ActuarialValuation



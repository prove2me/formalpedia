-- Prove2me | Definitions.Def_actuarial_whObjectiveOne
-- name    : actuarial_whObjectiveOne
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:13:16.842327+00:00
-- url     : https://prove2.me/theorems/576803e0-3fcd-4a51-b064-731e3f2aa905
-- title:
--   Composite graduation objective and invariance: whObjectiveOne
-- statement:
--   Whittaker-Henderson trade-off penalises lack of fit and age-to-age roughness. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   J_1=F+\lambda S_1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def whObjectiveOne (fit smoothness lambda : ℝ) : ℝ := fit + lambda*smoothness

end ActuarialValuation



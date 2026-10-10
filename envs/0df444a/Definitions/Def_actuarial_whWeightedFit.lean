-- Prove2me | Definitions.Def_actuarial_whWeightedFit
-- name    : actuarial_whWeightedFit
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:11:48.200127+00:00
-- url     : https://prove2.me/theorems/1ec7adef-58ae-45cc-97fb-6773ee7dc132
-- title:
--   Observed crude rates and exposure-weighted fitting: whWeightedFit
-- statement:
--   Statistical exposure weight controls how strongly the graduated rate should fit crude experience. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F_x=w_x(g_x-q_x)^2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSquaredResidual

namespace ActuarialValuation

noncomputable def whWeightedFit (weight graduated crude : ℝ) : ℝ := weight * whSquaredResidual graduated crude

end ActuarialValuation



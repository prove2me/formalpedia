-- Prove2me | Definitions.Def_actuarial_whRateResidual
-- name    : actuarial_whRateResidual
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:11:27.520512+00:00
-- url     : https://prove2.me/theorems/d76cbbde-57fd-46bf-b5c9-79c45b720bf0
-- title:
--   Observed crude rates and exposure-weighted fitting: whRateResidual
-- statement:
--   Graduation residual is the difference between graduated and observed crude rates. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   e_x=g_x-q_x
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def whRateResidual (graduated crude : ℝ) : ℝ := graduated - crude

end ActuarialValuation



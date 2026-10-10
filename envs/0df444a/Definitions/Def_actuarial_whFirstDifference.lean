-- Prove2me | Definitions.Def_actuarial_whFirstDifference
-- name    : actuarial_whFirstDifference
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:12:25.543959+00:00
-- url     : https://prove2.me/theorems/2c5c0c56-ec73-4aad-ab21-c5f24c2e451b
-- title:
--   First and second finite difference smoothness: whFirstDifference
-- statement:
--   Forward difference records change in graduated mortality between adjacent ages. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \Delta g_i=g_{i+1}-g_i
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def whFirstDifference (g : ℕ → ℝ) (i : ℕ) : ℝ := g (i+1)-g i

end ActuarialValuation



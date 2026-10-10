-- Prove2me | Definitions.Def_actuarial_whShiftedCurve
-- name    : actuarial_whShiftedCurve
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:13:32.649978+00:00
-- url     : https://prove2.me/theorems/1c0df5db-4269-4491-a214-b94b3d2ed786
-- title:
--   Composite graduation objective and invariance: whShiftedCurve
-- statement:
--   Uniformly shifting all graduated mortality levels preserves differences but changes fit to fixed crude rates. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_i^*=g_i+c
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ActuarialValuation

noncomputable def whShiftedCurve (g : ℕ → ℝ) (shift : ℝ) (i : ℕ) : ℝ := g i + shift

end ActuarialValuation



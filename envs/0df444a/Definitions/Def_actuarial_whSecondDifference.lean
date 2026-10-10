-- Prove2me | Definitions.Def_actuarial_whSecondDifference
-- name    : actuarial_whSecondDifference
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:12:37.494828+00:00
-- url     : https://prove2.me/theorems/ba421d5e-3ec8-4ae5-9f54-3ff8747f7ae7
-- title:
--   First and second finite difference smoothness: whSecondDifference
-- statement:
--   Second forward difference measures how successive age-to-age increments change. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \Delta^2g_i=g_{i+2}-2g_{i+1}+g_i
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFirstDifference

namespace ActuarialValuation

noncomputable def whSecondDifference (g : ℕ → ℝ) (i : ℕ) : ℝ := whFirstDifference g (i+1)-whFirstDifference g i

end ActuarialValuation



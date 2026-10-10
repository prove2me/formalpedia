-- Prove2me | Definitions.Def_actuarial_whFirstRoughness
-- name    : actuarial_whFirstRoughness
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:12:51.43193+00:00
-- url     : https://prove2.me/theorems/9fb17717-528c-4a2c-a88b-947198f90201
-- title:
--   First and second finite difference smoothness: whFirstRoughness
-- statement:
--   One-step roughness penalises variation in the mortality rates themselves. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S_1=\sum_{i<n}(\Delta g_i)^2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whFirstDifference

namespace ActuarialValuation

noncomputable def whFirstRoughness (g : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, (whFirstDifference g i)^2

end ActuarialValuation



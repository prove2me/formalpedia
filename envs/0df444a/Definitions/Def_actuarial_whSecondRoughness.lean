-- Prove2me | Definitions.Def_actuarial_whSecondRoughness
-- name    : actuarial_whSecondRoughness
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:13:07.857569+00:00
-- url     : https://prove2.me/theorems/2d1b751b-91f5-4ba7-9d56-aa08193a65e5
-- title:
--   First and second finite difference smoothness: whSecondRoughness
-- statement:
--   Two-step roughness penalises variation in the trend of graduated mortality rates. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S_2=\sum_{i<n}(\Delta^2g_i)^2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSecondDifference

namespace ActuarialValuation

noncomputable def whSecondRoughness (g : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, (whSecondDifference g i)^2

end ActuarialValuation



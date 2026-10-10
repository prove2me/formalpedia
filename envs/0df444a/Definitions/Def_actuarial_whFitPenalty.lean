-- Prove2me | Definitions.Def_actuarial_whFitPenalty
-- name    : actuarial_whFitPenalty
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T10:12:09.547543+00:00
-- url     : https://prove2.me/theorems/5ca37963-12f8-45dd-a9a2-ae68d5658a22
-- title:
--   Observed crude rates and exposure-weighted fitting: whFitPenalty
-- statement:
--   Overall fidelity loss sums exposure-weighted squared graduation errors over finite ages. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   F=\sum_{i<n}w_i(g_i-q_i)^2
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 156. Casualty Actuarial Society (1968), Proceedings of the Casualty Actuarial Society Volume LV, Graduation section, https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf; Nels M. Valerius, Notes on Whittaker-Henderson Formula A, Proceedings of the Casualty Actuarial Society LIV (1967), p. 218, https://www.casact.org/sites/default/files/database/proceed_proceed67_67218.pdf. Parent topic: Actuarial graduation of crude mortality estimates, exposure-weighted data fidelity, first and second order finite difference roughness penalties. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/proceed_proceed68_1968.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whWeightedFit

namespace ActuarialValuation

noncomputable def whFitPenalty (weight graduated crude : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, whWeightedFit (weight i) (graduated i) (crude i)

end ActuarialValuation



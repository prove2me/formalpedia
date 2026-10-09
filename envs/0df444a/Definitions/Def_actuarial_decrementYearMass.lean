-- Prove2me | Definitions.Def_actuarial_decrementYearMass
-- name    : actuarial_decrementYearMass
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T09:59:11.119862+00:00
-- url     : https://prove2.me/theorems/bfd0778f-6acd-4ff0-9dfb-7fb6254a20b4
-- title:
--   Probability mass of all mutually exclusive causes in a year
-- statement:
--   All termination causes in a policy year are mutually exclusive categorical outcomes. The aggregate annual decrement probability mass is the finite sum over labelled causes, retaining the ability to assign distinct benefits and reserve shocks to each cause.
--
--   **Mathematical statement**
--
--   $$
--   D_t=\sum_{c\in C}w_{t,c}
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib

namespace ActuarialValuation

noncomputable def decrementYearMass {C : Type*} [Fintype C]
  (w : ℕ → C → ℝ) (t : ℕ) : ℝ := ∑ c : C, w t c

end ActuarialValuation



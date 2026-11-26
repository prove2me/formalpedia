-- Prove2me | Definitions.Def_Tablet_surgeryPotential
-- name    : Tablet_surgeryPotential
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:58:31.539979+00:00
-- url     : https://prove2.me/theorems/9aa32276-fbd7-55f5-bc5c-fc7b4c032539
-- title:
--   surgery Potential
-- statement:
--   Definitions and structural lemmas for surgery Potential, from Daniel Spector (Inspectordaniel/metric-surgery-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Atomic decomposition of one-dimensional metric currents without boundary development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/surgeryPotential.lean

import Definitions.Def_Tablet_Preamble
set_option autoImplicit false
noncomputable def surgeryPotential (ε δ : ℝ) (n : ℕ) (L : ℝ) (m : ℕ) : ℝ :=
-- BODY
  (1 + 2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n : ℝ) * (1 - ε))) * L + (4 * ε⁻¹ * δ / (n : ℝ)) * m



-- Prove2me | Definitions.Def_FirstPassageLinearTransport_HeadlineParameters
-- name    : FirstPassageLinearTransport_HeadlineParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:13:43.874786+00:00
-- url     : https://prove2.me/theorems/418768dd-0100-5791-8957-51b227250047
-- title:
--   Headline Parameters
-- statement:
--   Definitions and structural lemmas for Headline Parameters, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/HeadlineParameters.lean

import Definitions.Def_FirstPassageLinearTransport_Constants
set_option autoImplicit true
namespace FirstPassageLinearTransport
open scoped Real
noncomputable section
def clockThreshold : ℝ :=
  1 - 1 / ((6953 / 1000 : ℝ) * Real.log 2)
structure HeadlineScalars (delta : ℝ) where
  r : ℝ
  chi : ℝ
  omega : ℝ
  eta : ℝ
  a0_lt_r : a0 < r
  r_lt_clock : r < clockThreshold
  r_lt_one : r < 1
  chi_pos : 0 < chi
  chi_lt_r : chi < r
  chi_le_one : chi ≤ 1
  omega_pos : 0 < omega
  density_compat : omega * Real.log (1 / chi) < 1
  descent_compat : delta < omega * Real.log (1 / r)
  eta_pos : 0 < eta
  eta_gap : eta < r - a0
structure QuantitativeHeadlineScalars (delta sigma : ℝ)
    extends HeadlineScalars delta where
  density_margin :
    omega * Real.log (1 / chi) < 1 - sigma
end
end FirstPassageLinearTransport



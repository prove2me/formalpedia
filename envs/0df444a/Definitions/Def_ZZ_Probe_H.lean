-- Prove2me | Definitions.Def_ZZ_Probe_H
-- name    : ZZ_Probe_H
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-26T13:46:59.819981+00:00
-- url     : https://prove2.me/theorems/8eb4edf4-97c8-4f9e-a394-bc8eb104b4fd
-- title:
--   ZZ probe ZZ_Probe_H
-- statement:
--   Automated importability probe ZZ_Probe_H. No mathematics.

import Mathlib
import Definitions.Def_Thm_BraidsLinksMCG_hub_frac_ne_int

open BraidsLinksMCG

theorem probe : ∀ n : ℕ, (n : ℝ) + 2/3 < (n : ℝ) + 1 := by
  intro n
  exact leftHub_re n |>.1



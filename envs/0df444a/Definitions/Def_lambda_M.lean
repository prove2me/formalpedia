-- Prove2me | Definitions.Def_lambda_M
-- name    : lambda_M
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:33:52.099395+00:00
-- url     : https://prove2.me/theorems/836c4ffa-ed83-484f-9bec-f0fb5c7f884c
-- title:
--   lambda_M
-- statement:
--   The Monster wavelength $\lambda_M = \frac{\ln|\mathbb{M}|}{2\pi}$.

import Definitions.Def_lnMonster
import Mathlib

noncomputable def lambda_M : ℝ := lnMonster / (2 * Real.pi)



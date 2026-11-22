-- Prove2me | Definitions.Def_phi
-- name    : phi
-- status  : Definition
-- author  : @@bwdaugherty
-- created : 2026-11-22T03:20:54.331232+00:00
-- url     : https://prove2.me/theorems/38889aef-598b-4b42-b8c8-c5d18bf183f2
-- title:
--   phi
-- statement:
--   The golden ratio $\varphi = \frac{1 + \sqrt{5}}{2}$.

import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable def φ : ℝ := (1 + Real.sqrt 5) / 2



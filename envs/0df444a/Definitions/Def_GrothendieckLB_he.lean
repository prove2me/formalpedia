-- Prove2me | Definitions.Def_GrothendieckLB_he
-- name    : GrothendieckLB_he
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:39.151207+00:00
-- url     : https://prove2.me/theorems/25fb86de-3f4e-4ca5-b43a-97d37b800464
-- title:
--   Orthonormal Hermites $\mathrm{He}_0,\dots,\mathrm{He}_3$
-- statement:
--   The orthonormal one-dimensional Hermite functions of degree at most three:
--   $$
--   \mathrm{He}_0=1,\quad\mathrm{He}_1(s)=s,\quad\mathrm{He}_2(s)=\frac{s^2-1}{\sqrt2},\quad\mathrm{He}_3(s)=\frac{s^3-3s}{\sqrt6}.
--   $$
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.30

import Mathlib

namespace GrothendieckLB

/-- The orthonormal one-dimensional Hermites `He₀ = 1`, `He₁(s) = s`, `He₂(s) = (s² − 1)/√2`,
`He₃(s) = (s³ − 3s)/√6` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.30). -/
noncomputable def he : Fin 4 → ℝ → ℝ
  | 0, _ => 1
  | 1, s => s
  | 2, s => (s ^ 2 - 1) / Real.sqrt 2
  | 3, s => (s ^ 3 - 3 * s) / Real.sqrt 6

end GrothendieckLB



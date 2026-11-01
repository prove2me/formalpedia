-- Prove2me | Definitions.Def_TSDRiem_etaPrime
-- name    : TSDRiem_etaPrime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:33.227959+00:00
-- url     : https://prove2.me/theorems/80f48b05-cc0b-44c0-9d84-c8ff2ec28f19
-- title:
--   Far-step decrease constant $\eta'$ of Lemma 4.4 and Theorem 4.5
-- statement:
--   The decrease constant for inner loops that travel farther than $r$ is
--
--   $$
--   \eta':=\frac{L_{\min}\,r^2}{2m} .
--   $$
--
--   By Lemma 4.4, an outer iteration whose inner steps have total length more than $r$ decreases $f$ by at least $\eta'$; hence there are at most $(f(x^1)-f^*)/\eta'$ such iterations.
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Lemma 4.4, p.13; Theorem 4.5, p.14

import Mathlib
import Definitions.Def_TSDRiem_Lmin

namespace TSDRiem

/-- The far-step decrease constant of Lemma 4.4 and Theorem 4.5, `η′ := L_min r² / (2m)`.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Lemma 4.4, p.13,
and Theorem 4.5, p.14. -/
noncomputable def etaPrime (m : ℕ) (L : Fin m → ℝ) (r : ℝ) : ℝ := Lmin L * r ^ 2 / (2 * m)

end TSDRiem



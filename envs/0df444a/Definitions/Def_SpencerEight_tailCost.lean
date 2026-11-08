-- Prove2me | Definitions.Def_SpencerEight_tailCost
-- name    : SpencerEight_tailCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:39.454984+00:00
-- url     : https://prove2.me/theorems/8b1466bc-b7e1-46ac-887d-99d72047e6a8
-- title:
--   Tail cost $\mathcal T_s(v)$, Eq. (90)
-- statement:
--   With $U:=-\log v$, $q_T:=0.011$, $r_T:=\sqrt{q_T}$ and $\lambda:=-\log q_T$,
--   $$\mathcal T_s(v):=\frac{185}{s}\sqrt v\Bigl(\frac{U}{1-r_T}+\frac{\lambda r_T}{(1-r_T)^2}\Bigr).$$
--   It is the normalized cost of signing a residual family of at most $vn$ matrices.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.21, Eq. (90), p.84 (PDF p.84)

import Mathlib

namespace SpencerEight

/-- The tail cost `T_s(v) := (185/s) √v (U/(1 − r_T) + λ r_T/(1 − r_T)²)` of Eq. (90) (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.21, p.84 (PDF p.84)), with `U := −log v`, `q_T := 0.011`, `r_T := √q_T`, `λ := −log q_T`.

**Formalization Note** Every use has `s > 0` and `0 < v < e^{−731/256}`, so the logarithm and the square root have positive arguments. -/
noncomputable def tailCost (s v : ℝ) : ℝ :=
  185 / s * Real.sqrt v *
    (-Real.log v / (1 - Real.sqrt 0.011) +
      -Real.log 0.011 * Real.sqrt 0.011 / (1 - Real.sqrt 0.011) ^ 2)

end SpencerEight



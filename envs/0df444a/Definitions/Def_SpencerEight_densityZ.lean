-- Prove2me | Definitions.Def_SpencerEight_densityZ
-- name    : SpencerEight_densityZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:27.444214+00:00
-- url     : https://prove2.me/theorems/4a7dfcca-c6de-45f1-a1c6-affbf55b3068
-- title:
--   Coding density $f_Z$
-- statement:
--   The even function
--   $$f_Z(z):=\begin{cases}a,&|z|\le s,\\ b(2s-|z|),&s<|z|\le 2s,\\ 0,&|z|>2s,\end{cases}\qquad b=\frac{1-2sa}{s^2}.$$
--   At $(s,a)=(s_\star,a_\star)$ this is the density of the variable $Z$ of Section 8.1; Lemma 8.42 uses the same family at the refined parameters. The identity $2sa+s^2b=1$ normalizes it.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.1, p.69 (PDF p.69)

import Mathlib
import Definitions.Def_SpencerEight_codingB

namespace SpencerEight

/-- The even density of the coding variable `Z` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.1, p.69 (PDF p.69)): `f_Z(z) = a` for `|z| ≤ s`, `b(2s − |z|)` for `s < |z| ≤ 2s`, and `0` for `|z| > 2s`, with `b = (1 − 2sa)/s²`. The page fixes `(s, a) = (s⋆, a⋆)`; Lemma 8.42 and the proof of Lemma 8.2 use the same family at other parameters. -/
noncomputable def densityZ (s a z : ℝ) : ℝ :=
  if |z| ≤ s then a else if |z| ≤ 2 * s then codingB s a * (2 * s - |z|) else 0

end SpencerEight



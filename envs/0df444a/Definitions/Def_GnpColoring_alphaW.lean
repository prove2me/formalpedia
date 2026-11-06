-- Prove2me | Definitions.Def_GnpColoring_alphaW
-- name    : GnpColoring_alphaW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:24.277613+00:00
-- url     : https://prove2.me/theorems/65cbc668-9211-4adb-80bb-39789de157e5
-- title:
--   The weight base $\alpha=C\log d$
-- statement:
--   For real $C$ and $d$, the base of the vertex weights is
--
--   $$\alpha = C\log d$$
--
--   (natural logarithm). Section 3.1 assumes $\alpha>1$ throughout; statements that need it carry it as a hypothesis.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 3.1, p.15

import Mathlib

open scoped Classical
open Finset

namespace GnpColoring

/-- **The weight base** `α := C log d` (natural logarithm).

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 3.1, p.15: "α := C log d > 1". The condition `α > 1` is a standing hypothesis
of Section 3, stated separately wherever it is used. -/
noncomputable def alphaW (C d : ℝ) : ℝ := C * Real.log d

end GnpColoring



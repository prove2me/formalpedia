-- Prove2me | Definitions.Def_GnpColoring_rBreakpoints
-- name    : GnpColoring_rBreakpoints
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:52.438375+00:00
-- url     : https://prove2.me/theorems/bb6216bf-089d-4df0-8812-2c5b15a62f92
-- title:
--   The $r$-breakpoints $\hat S_r$
-- statement:
--   For an integer $r\ge0$, $\hat S_r$ is the set of vertices from which no heavy path with at most $r$ edges starts, i.e. the $r$-breakpoints. Always $\hat S\subseteq\hat S_r$; Theorem 4.2 (iii) shows equality for $r\ge h$ with high probability.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 4, p.35

import Mathlib
import Definitions.Def_GnpColoring_IsRBreakpoint

open scoped Classical
open Finset

namespace GnpColoring

/-- **The r-breakpoints** `Ŝ_r`: the vertices from which no heavy path of at most `r` edges
starts.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 4, p.35: "Write Ŝ for the set of global breakpoints, and Ŝ_r for the set of
vertices from which no heavy path of at most r edges starts. Thus Ŝ ⊆ Ŝ_r." -/
noncomputable def rBreakpoints {n : ℕ} (G : SimpleGraph (Fin n)) (d η A C : ℝ) (r : ℕ) :
    Finset (Fin n) :=
  univ.filter fun v => IsRBreakpoint G d η A C r v

end GnpColoring



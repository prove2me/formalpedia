-- Prove2me | Definitions.Def_GnpColoring_globalBreakpoints
-- name    : GnpColoring_globalBreakpoints
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:45.632137+00:00
-- url     : https://prove2.me/theorems/aad2f487-cec2-46db-a1a9-ecfec385619e
-- title:
--   The global breakpoints $\hat S$
-- statement:
--   A vertex is a **global breakpoint** if it is an $r$-breakpoint for every $r\ge0$, equivalently if no path of weight $>1$ (a *heavy* path) starts at it. $\hat S$ denotes the set of global breakpoints. Singletons of a block partition are chosen among them.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Definition 3.1, p.15; Section 4, p.35

import Mathlib
import Definitions.Def_GnpColoring_IsRBreakpoint

open scoped Classical
open Finset

namespace GnpColoring

/-- **The global breakpoints** `Ŝ`: the vertices that are `r`-breakpoints for every `r`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Definition 3.1, p.15: "We say that v is a global breakpoint if it is an r-breakpoint for
all r." Section 4, p.35: "A vertex is a global breakpoint if no heavy path starts there. Write Ŝ
for the set of global breakpoints." -/
noncomputable def globalBreakpoints {n : ℕ} (G : SimpleGraph (Fin n)) (d η A C : ℝ) :
    Finset (Fin n) :=
  univ.filter fun v => ∀ r : ℕ, IsRBreakpoint G d η A C r v

end GnpColoring



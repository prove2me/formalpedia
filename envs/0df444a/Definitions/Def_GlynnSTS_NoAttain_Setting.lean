-- Prove2me | Definitions.Def_GlynnSTS_NoAttain_Setting
-- name    : GlynnSTS_NoAttain_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:08:00.324019+00:00
-- url     : https://prove2.me/theorems/f8287b15-7acf-467e-8c77-9741e6660f2c
-- title:
--   Proof of Proposition 4.26, p. 13 — the subspace C₀[0,1] = {x ∈ C[0,1] : x(0) = 0}
-- statement:
--   Let $C[0,1]$ be the space of continuous real functions on $[0,1]$ with the uniform metric $\rho(x,y)=\sup_{0\le t\le1}|x(t)-y(t)|$. The paths starting at the origin form the subset
--   $$C_0[0,1] \equiv \{x \in C[0,1] : x(0) = 0\}.$$
--
--   The proof of Proposition 4.26 shows that for every $x \in C_0[0,1]$ the scaled Brownian motion $\sigma B$ charges every $\rho$-ball around $x$, and concludes that a $g \in \mathcal M$ satisfying (4.25) is discontinuous at every point of $C_0[0,1]$. Since a standard Brownian motion starts at $0$, $B \in C_0[0,1]$ almost surely.
--
--   **Formalization Note** $C[0,1]$ is `C(unitInterval, ℝ)`. The other objects of the mission — the Borel $\sigma$-algebra on $C[0,1]$, the path $k(t)=t$, the discontinuity set $D(g)$, the standard Brownian motion $B$, the class $\mathcal M$ of (2.3), $X_n$, Assumption (2.1), $H$ and $L_n$ — are the shared definitions `GlynnSTS.Limit.Setting` and `GlynnSTS.Length.Setting` of this paper, which this file imports; only $C_0[0,1]$ is new here.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), p. 13, proof of Proposition 4.26 (definition of C₀[0,1] before (4.27))

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting
import Definitions.Def_GlynnSTS_Limit_Setting

namespace GlynnSTS.NoAttain

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- `C₀[0,1] = {x ∈ C[0,1] : x(0) = 0}`. -/
def C0 : Set C(unitInterval, ℝ) := {x | x 0 = 0}

end GlynnSTS.NoAttain



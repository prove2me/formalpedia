-- Prove2me | Definitions.Def_GibbsCongestion_restrictDist
-- name    : GibbsCongestion_restrictDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:01:32.530343+00:00
-- url     : https://prove2.me/theorems/3ba1ff80-dbf3-40e7-a3d9-1196721c0623
-- title:
--   Stationary distribution $\pi_i=\pi/\bar\pi(i)$ of the restriction chain
-- statement:
--   For a class $\Omega_i$ of a partition, $\pi_i(x)=\pi(x)/\bar\pi(i)$ for $x\in\Omega_i$: the conditional distribution of $\pi$ on $\Omega_i$, the stationary distribution of the restriction chain $P_i$.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.4, p.11

import Mathlib
import Definitions.Def_GibbsCongestion_projDist

namespace GibbsCongestion

/-- The stationary distribution `π_i(x) = π(x)/π̄(i)` of the restriction chain on `Ω_i`
(Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.4, p.11). -/
noncomputable def restrictDist {Ω ι : Type*} [Fintype Ω] [DecidableEq ι] (π : Ω → ℝ)
    (cls : Ω → ι) (i : ι) : {x // cls x = i} → ℝ :=
  fun x => π x.1 / projDist π cls i

end GibbsCongestion



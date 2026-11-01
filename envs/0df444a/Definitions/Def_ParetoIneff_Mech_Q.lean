-- Prove2me | Definitions.Def_ParetoIneff_Mech_Q
-- name    : ParetoIneff_Mech_Q
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:03.797722+00:00
-- url     : https://prove2.me/theorems/f2e0ba3d-800c-46d9-888c-7b6a991e02c6
-- title:
--   Equilibrium set $\mathcal Q_t^{\mathcal M}$
-- statement:
--   $\mathcal Q_t^{\mathcal M}$ is the set of pure Nash equilibria of the mechanism $\mathcal M$ with respect to the true $n\times m$ profile $t$. The suprema and infima in the Price of Anarchy and the Price of Stability range over this set.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, §2, p.5

import Mathlib
import Definitions.Def_ParetoIneff_Mech_IsEq

open NNReal

namespace ParetoIneff

/-- The set `𝒬_t^ℳ` of pure Nash equilibria of `ℳ` with respect to the true `n × m` profile `t`,
arXiv:1809.03454v7, p.5. -/
def Mech.Q {n : ℕ} (M : Mech n) (m : ℕ) (t : Fin n → Fin m → ℝ≥0) :
    Set (Fin n → Fin m → ℝ≥0) :=
  {s | M.IsEq m t s}

end ParetoIneff



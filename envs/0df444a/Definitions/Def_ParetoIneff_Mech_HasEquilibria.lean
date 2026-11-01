-- Prove2me | Definitions.Def_ParetoIneff_Mech_HasEquilibria
-- name    : ParetoIneff_Mech_HasEquilibria
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:28:10.187424+00:00
-- url     : https://prove2.me/theorems/1918b00e-c808-485d-a52e-2034203b06ae
-- title:
--   Equilibria exist at every profile
-- statement:
--   The standing assumption of the paper: a mechanism is considered only if Nash equilibria exist for every profile of processing times, that is
--   $$
--   \mathcal Q_t^{\mathcal M}\neq\emptyset\qquad\text{for all } m \text{ and all } t\in\mathbb R_{\ge0}^{n\times m}.
--   $$
--   Without it the Price of Stability would be infinite for the trivial reason that a profile has no equilibrium.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, §2, p.5

import Mathlib
import Definitions.Def_ParetoIneff_Mech_Q

open NNReal

namespace ParetoIneff

/-- The standing assumption of arXiv:1809.03454v7, p.5: Nash equilibria exist for every profile of
processing times, `𝒬_t^ℳ ≠ ∅` for every `m` and every `t ∈ ℝ≥0^{n×m}`. -/
def Mech.HasEquilibria {n : ℕ} (M : Mech n) : Prop :=
  ∀ (m : ℕ) (t : Fin n → Fin m → ℝ≥0), (M.Q m t).Nonempty

end ParetoIneff



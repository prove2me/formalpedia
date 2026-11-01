-- Prove2me | Definitions.Def_EThetaPoula_Risk_IsStandardBrownian
-- name    : EThetaPoula_Risk_IsStandardBrownian
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:22:22.709202+00:00
-- url     : https://prove2.me/theorems/48eeb538-0cfc-42f9-bbf4-db8ba6c9bcb6
-- title:
--   Standard $d$-dimensional Brownian motion independent of the data
-- statement:
--   $B=(B_t)_{t\ge0}$ is a standard $d$-dimensional Brownian motion: its coordinates are independent real Brownian motions with almost surely continuous paths. It is independent of the initial condition and the data $(\theta_0,(X_n)_n)$, as the paper requires of its natural filtration.
--
--   **Formalization Note** Coordinates use Mathlib's `IsBrownianReal`. The published `EthierKurtz_IsStandardBrownian` requires every path to be continuous, which this paper does not, so it is not reused.
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, §6.1, p.22, after (37)

import Mathlib
import Definitions.Def_EThetaPoula_Risk_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- `B` is a standard `d`-dimensional Brownian motion, as `(B_t)_{t≥0}` of (37), Lim, Neufeld,
Sabanis, Zhang, arXiv:2210.13193v3, §6.1, p.22, independent of the data `(θ₀, (X_n)_n)` of the
model (the paper: `F_t` is independent of `G_∞ ∨ σ(θ₀)`).

**Formalization Note.** Each coordinate is Mathlib's `IsBrownianReal` (almost surely continuous
paths) and the coordinates are independent as processes. -/
structure Model.IsStandardBrownian {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (B : ℝ≥0 → Ω → Eucl d) : Prop where
  /-- each coordinate is a real Brownian motion -/
  coord : ∀ i, IsBrownianReal (fun t ω => B t ω i) S.P
  /-- the coordinates are independent processes -/
  indep_coord : iIndepFun (fun (i : Fin d) ω t => B t ω i) S.P
  /-- `B` is independent of `(θ₀, (X_n)_n)` -/
  indep_data : IndepFun (fun ω t => B t ω) (fun ω => (S.θ₀ ω, fun n => S.X n ω)) S.P

end EThetaPoula.Risk



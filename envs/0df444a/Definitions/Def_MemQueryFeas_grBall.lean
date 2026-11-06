-- Prove2me | Definitions.Def_MemQueryFeas_grBall
-- name    : MemQueryFeas_grBall
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:35:39.574222+00:00
-- url     : https://prove2.me/theorems/a6f21415-78a4-44a5-b68f-8dfb3c850085
-- title:
--   Ball $B(F,\rho)$ in the Grassmannian
-- statement:
--   For $F\in\mathrm{Gr}(k,d)$ and $\rho\ge0$,
--   $$
--   B(F,\rho)=\{E\in\mathrm{Gr}(k,d):\ \theta_{\max}(E,F)\le\rho\}.
--   $$
--   Balls in the Grassmannian are taken for the largest-principal-angle distance.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Notations, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MemQueryFeas_IsOrthProj
import Definitions.Def_MemQueryFeas_thetaMax

namespace MemQueryFeas

/-- **Ball in the Grassmannian.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Notations, p.7 (PDF p.8): "for any center `F ∈ Gr(k, d)` and
radius `ρ ∈ [0, π/2]` we denote `B(F, ρ) := {E ∈ Gr(k, d) : θ_max(E, F) ≤ ρ}`".

**Formalization Note.** Elements are projections `p = P_E` of rank `k`. -/
def grBall {d : ℕ} (k : ℕ) (F : Op d) (ρ : ℝ) : Set (Op d) :=
  {p | IsOrthProj k p ∧ thetaMax p F ≤ ρ}

end MemQueryFeas



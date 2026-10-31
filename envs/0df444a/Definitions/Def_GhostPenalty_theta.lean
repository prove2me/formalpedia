-- Prove2me | Definitions.Def_GhostPenalty_theta
-- name    : GhostPenalty_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:17.964433+00:00
-- url     : https://prove2.me/theorems/94b3ceb2-f337-4b0f-bfc1-b065fd3afc8a
-- title:
--   The stationarity measure $\theta(x)$, (14)
-- statement:
--   For $x\in K$,
--   $$\theta(x)\triangleq\max_i\{g_i(x)_+\}-\kappa(x)=\lambda\Big(\max_i\{g_i(x)_+\}-\min_d\Big\{\max_i\{\tilde g_i(d;x)_+\}\ \Big|\ \|d\|_\infty\le\rho,\ d\in K-x\Big\}\Big). \tag{14}$$
--   $\theta$ is a stationarity measure for the violation problem (4) (Proposition 3).
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, (14), p.11

import Mathlib
import Definitions.Def_GhostPenalty_kappa

namespace GhostPenalty

/-- **The stationarity measure `θ(x)`**, (14).
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §3, (14), p.11: "The quantity
`θ(x) ≜ max_i{g_i(x)+} − κ(x) = λ[ max_i{g_i(x)+} − min_d { max_i{g̃_i(d;x)+} | ‖d‖∞ ≤ ρ,
d ∈ K − x } ]` (14)".

**Formalization Note.** Defined by the first expression of (14); the second is equal to it by
(8). -/
noncomputable def theta {n m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gt : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (lam ρ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  posMax g x - kappa g gt K lam ρ x

end GhostPenalty



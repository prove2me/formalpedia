-- Prove2me | Definitions.Def_TeschlODE_Planar_orbit
-- name    : TeschlODE_Planar_orbit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T14:37:36.746688+00:00
-- url     : https://prove2.me/theorems/2c5ab075-632c-4d9e-b5eb-a04a8628b6f8
-- title:
--   Orbit γ(x) of a point, Eq. (6.15)
-- statement:
--   The **orbit** of $x$ under the flow $\Phi$ of $\dot x = f(x)$ on $M$ is
--   $$\gamma(x) = \Phi(I_x \times \{x\}) = \{\Phi(t, x) : t \in I_x\} \subseteq M.$$
--
--   Orbits partition $M$; an orbit is a *fixed orbit* $\{x_0\}$ ($f(x_0) = 0$), a *regular periodic orbit*, or a *non-closed orbit* (p. 192).
--
--   **Formalization Note.** Points are `Fin n → ℝ`; the image is taken over `lifetime f M x`, so it is empty for $x \notin M$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 192, §6.3, Eq. (6.15)

import Mathlib
import Definitions.Def_TeschlODE_Planar_flow

namespace TeschlODE.Planar

/-- Teschl, §6.3, (6.15), p. 192: the orbit `γ(x) = Φ(I_x × {x})` of `x` under the flow of
`ẋ = f(x)` on `M`. -/
def orbit {n : ℕ} (f : (Fin n → ℝ) → Fin n → ℝ) (M : Set (Fin n → ℝ)) (x : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  (fun t => flow f M t x) '' lifetime f M x

end TeschlODE.Planar



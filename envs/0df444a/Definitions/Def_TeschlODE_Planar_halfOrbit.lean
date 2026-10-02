-- Prove2me | Definitions.Def_TeschlODE_Planar_halfOrbit
-- name    : TeschlODE_Planar_halfOrbit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T14:44:50.875176+00:00
-- url     : https://prove2.me/theorems/d8b3e0a1-829e-43be-8c69-c024aebf298c
-- title:
--   Forward and backward orbits γ_±(x), Eq. (6.16)
-- statement:
--   For $\sigma \in \{+, -\}$ the **forward** ($\sigma = +$) and **backward** ($\sigma = -$) orbit of $x$ are
--   $$\gamma_\pm(x) = \Phi\big((0, T_\pm(x)), x\big),$$
--   i.e. the points $\Phi(t, x)$ with $t \in I_x$ and $t > 0$ (resp. $t < 0$). A set $U \subseteq M$ is $\sigma$ invariant if $\gamma_\sigma(x) \subseteq U$ for all $x \in U$ (6.17).
--
--   **Formalization Note.** $\sigma$ is a `Bool`: `true` is the book's $+$, `false` its $-$. The point $x$ itself is not included at $t = 0$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 192, §6.3, Eq. (6.16)

import Mathlib
import Definitions.Def_TeschlODE_Planar_flow

namespace TeschlODE.Planar

/-- Teschl, §6.3, (6.16), p. 192: the forward (`σ = true`, the book's `+`) or backward
(`σ = false`, the book's `−`) orbit `γ_σ(x) = Φ((0, T_σ(x)), x)`, i.e. the points `Φ(t, x)` with
`t ∈ I_x` and `t > 0` (resp. `t < 0`). The point `x` itself is not included (it is only when the
orbit returns to it). -/
def halfOrbit {n : ℕ} (f : (Fin n → ℝ) → Fin n → ℝ) (M : Set (Fin n → ℝ)) (σ : Bool)
    (x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  (fun t => flow f M t x) '' {t | t ∈ lifetime f M x ∧ (if σ then 0 < t else t < 0)}

end TeschlODE.Planar



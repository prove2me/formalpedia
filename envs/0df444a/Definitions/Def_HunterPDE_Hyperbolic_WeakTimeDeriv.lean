-- Prove2me | Definitions.Def_HunterPDE_Hyperbolic_WeakTimeDeriv
-- name    : HunterPDE_Hyperbolic_WeakTimeDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:28:06.628562+00:00
-- url     : https://prove2.me/theorems/28aed33c-02a8-40a4-969e-29ab5c361b4a
-- title:
--   Weak time derivative of a vector-valued function (Eq. (6.14)) and weak continuity C_w([0,T]; V)
-- statement:
--   Let $X$ be a real Banach space and $T > 0$. A function $w : (0,T) \to X$ is the **weak time derivative** $u_t$ of $u : (0,T) \to X$ if $u$ and $w$ are locally Bochner-integrable on $(0,T)$ and
--   $$\int_0^T \varphi'(t)\,u(t)\,dt = -\int_0^T \varphi(t)\,w(t)\,dt \qquad \text{for every } \varphi \in C_c^\infty(0,T).$$
--   A function $u : [0,T] \to V$ into a normed space $V$ is **weakly continuous**, $u \in C_w([0,T];V)$, if $t \mapsto \langle \ell, u(t)\rangle$ is continuous on $[0,T]$ for every bounded linear functional $\ell \in V'$.
--
--   These are the notions of time derivative and of continuity used for the weak solution of the wave equation.
--
--   **Formalization Note.** Functions are defined on all of $\mathbb{R}$; only their values on $(0,T)$ (for derivatives) or $[0,T]$ (for continuity) matter. Local integrability is part of the definition, so the Bochner integrals are never the junk value $0$. The page prints (6.14) with $\varphi$ and $\varphi'$ interchanged; the definition here is the weak derivative that (6.14) is announced to generalise.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 180, Eq. (6.14); p. 217 (C_w([0,T]; V))

import Mathlib

namespace HunterPDE.Hyperbolic

open MeasureTheory Set
open scoped ContDiff

/-- Weak (distributional) time derivative of a vector-valued function on `(0, T)` (Hunter (6.14),
§6.A): `w` is the weak derivative `u_t` of `u : (0, T) → X` if `u` and `w` are locally (Bochner)
integrable on `(0, T)` and
`∫₀ᵀ φ'(t) u(t) dt = −∫₀ᵀ φ(t) w(t) dt` for every `φ ∈ C_c^∞(0, T)`.
(The page prints (6.14) with `φ` and `φ'` interchanged; the version here is the definition of a
weak derivative that (6.14) is announced as generalising.) -/
def HasWeakTimeDeriv {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : ℝ) (u w : ℝ → X) : Prop :=
  LocallyIntegrableOn u (Ioo 0 T) ∧ LocallyIntegrableOn w (Ioo 0 T) ∧
    ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo 0 T →
      ∫ t in Ioo 0 T, deriv φ t • u t = -∫ t in Ioo 0 T, φ t • w t

/-- Weak continuity on `[0, T]` (`u ∈ C_w([0, T]; V)`): for every bounded linear functional
`ℓ ∈ V'`, the real function `t ↦ ⟨ℓ, u(t)⟩` is continuous on `[0, T]`. -/
def WeaklyContinuousOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : ℝ) (u : ℝ → V) : Prop :=
  ∀ ℓ : StrongDual ℝ V, ContinuousOn (fun t => ℓ (u t)) (Icc 0 T)

end HunterPDE.Hyperbolic



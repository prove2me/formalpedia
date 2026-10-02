-- Prove2me | Definitions.Def_HunterPDE_Parabolic_WeakTimeDeriv
-- name    : HunterPDE_Parabolic_WeakTimeDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:16:22.938429+00:00
-- url     : https://prove2.me/theorems/94112cf5-996a-4203-83f6-ac8df6bb0f0d
-- title:
--   Distributional time derivative of a vector-valued function on (0, T) (Eq. (6.14))
-- statement:
--   Let $T \in \mathbb{R}$, let $X$ and $Y$ be real normed spaces with $Y$ complete, and let $\iota : X \to Y$ be a continuous linear map. A **test function on $(0, T)$** is a smooth $\phi : \mathbb{R} \to \mathbb{R}$ with compact support contained in $(0, T)$, i.e. $\phi \in C_c^\infty(0, T)$. A function $u : (0, T) \to X$ has **weak time derivative** $u_t = w : (0, T) \to Y$ (taken in $Y$, $u$ being read in $Y$ through $\iota$) if
--   $$\int_0^T \phi'(t)\,\iota(u(t))\,dt = -\int_0^T \phi(t)\,w(t)\,dt \qquad \text{for every } \phi \in C_c^\infty(0, T),$$
--   the integrals being Bochner integrals in $Y$. For $X = Y = \mathbb{R}$ and $\iota$ the identity this is the weak derivative of a real function on $(0, T)$.
--
--   **Formalization Note.** The page prints (6.14) as $\int_0^T \phi\,u\,dt = -\int_0^T \phi'\,w\,dt$, with $\phi$ and $\phi'$ interchanged; that version fails already for $u(t) = t$, $w = 1$. The definition uses the standard form, which is the one the proof of Theorem 6.41 (p. 209) uses. Completeness of $Y$ is required so that the Bochner integral is not identically zero. In every use the integrands are integrable (they are products of a bounded compactly supported scalar function with an $L^2(0,T;\cdot)$ function).
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 180, Eq. (6.14)

import Mathlib

namespace HunterPDE.Parabolic

open MeasureTheory
open scoped ContDiff

/-- A scalar test function on `(0, T)`: `φ ∈ C_c^∞(0, T)`, i.e. `φ : ℝ → ℝ` is smooth
(`ContDiff ℝ ∞`, not the analytic `ω`) with compact support contained in the open interval
`(0, T)`. -/
def IsTestFunctionOn (T : ℝ) (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Set.Ioo 0 T

/-- Distributional (weak) time derivative of a vector-valued function (Hunter, (6.14), p. 180, and
§6.A): `u : (0, T) → X` has weak derivative `u_t = w : (0, T) → Y` in `Y`, where `u` is read in
`Y` through the continuous linear embedding `ι : X → Y`, if
`∫₀ᵀ φ'(t) u(t) dt = −∫₀ᵀ φ(t) w(t) dt` (Bochner integrals in the Banach space `Y`)
for every `φ ∈ C_c^∞(0, T)`.

The page prints (6.14) as `∫ φ u = −∫ φ' w`, with `φ` and `φ'` interchanged; that is a typo (with
it, `w = u_t` fails already for `u(t) = t`), and the definition here uses the standard form, which
is the one the proof of Theorem 6.41 (p. 209) uses. For `ι = id` and `X = Y = ℝ` this is the
weak derivative of a real function on `(0, T)`. -/
def HasWeakTimeDeriv {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] (ι : X →L[ℝ] Y) (T : ℝ)
    (u : ℝ → X) (w : ℝ → Y) : Prop :=
  ∀ φ : ℝ → ℝ, IsTestFunctionOn T φ →
    ∫ t in Set.Ioo 0 T, deriv φ t • ι (u t) = -∫ t in Set.Ioo 0 T, φ t • w t

end HunterPDE.Parabolic



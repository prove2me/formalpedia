-- Prove2me | Definitions.Def_TeschlODE_Planar_IsPeriodicPoint
-- name    : TeschlODE_Planar_IsPeriodicPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T15:01:59.848928+00:00
-- url     : https://prove2.me/theorems/83c54da7-ce35-4f72-ac99-235024448e82
-- title:
--   Periodic point of a flow
-- statement:
--   A point $x$ is a **periodic point** of the flow $\Phi$ of $\dot x = f(x)$ on $M$ if
--   $$\exists\, T > 0,\ T \in I_x,\ \Phi(T, x) = x .$$
--
--   As in the book, a fixed point ($f(x) = 0$, period zero) is periodic. A **regular periodic orbit** is the orbit of a periodic point $x$ with $f(x) \neq 0$ (positive period), and a **non-closed orbit** is the orbit of a point that is not periodic (the classification (i)–(iii) on p. 192).
--
--   **Formalization Note.** The book's period $T(x) = \inf\{T > 0 : \Phi(T,x) = x\}$ is not needed: "regular periodic" is written as `IsPeriodicPoint f M x ∧ f x ≠ 0`, which is equivalent to positive period.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 192, §6.3

import Mathlib
import Definitions.Def_TeschlODE_Planar_flow

namespace TeschlODE.Planar

/-- Teschl, §6.3, p. 192: `x` is a periodic point of the flow of `ẋ = f(x)` on `M` if there is
some `T > 0` (in `I_x`) with `Φ(T, x) = x`. As in the book, fixed points (`f x = 0`, period zero)
are periodic; a *regular* periodic point is a periodic point with `f x ≠ 0` (positive period).
A point that is not periodic lies on a *non-closed* orbit. -/
def IsPeriodicPoint {n : ℕ} (f : (Fin n → ℝ) → Fin n → ℝ) (M : Set (Fin n → ℝ))
    (x : Fin n → ℝ) : Prop :=
  ∃ T : ℝ, 0 < T ∧ T ∈ lifetime f M x ∧ flow f M T x = x

end TeschlODE.Planar



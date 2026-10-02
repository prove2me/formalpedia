-- Prove2me | Definitions.Def_TeschlODE_PeriodicOrbits_IsRegularPeriodicPoint
-- name    : TeschlODE_PeriodicOrbits_IsRegularPeriodicPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T03:30:50.665545+00:00
-- url     : https://prove2.me/theorems/0b46506a-a097-45f6-b99d-88aac56e5241
-- title:
--   Periodic point with positive (least) period $T = T(x)$ — the standing assumption of §12.1
-- statement:
--   Let $\Phi$ be a flow with maximal intervals $I_x$. A point $x$ is a **periodic point with period** $T$ if
--   $$T > 0,\qquad T \in I_x,\qquad \Phi(T, x) = x,\qquad \Phi(t, x) \ne x \ \text{ for } 0 < t < T.$$
--   Thus $T = T(x) = \inf\{T > 0 \mid \Phi(T, x) = x\}$ is the book's period of $x$, and it is positive, i.e. $x$ lies on a regular periodic orbit rather than being a fixed point (which has period $0$).
--
--   This is the standing assumption of §12.1: "the differential equation $\dot x = f(x)$ has a periodic solution $\Phi(t, x_0)$ of period $T = T(x_0)$."
--
--   **Formalization Note.** Fixed points are excluded on purpose: at a fixed point there is no transversal section and the Poincaré map does not exist.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 192, §6.3 (period T(x)); p. 315, §12.1, Eq. (12.2)

import Mathlib

namespace TeschlODE.PeriodicOrbits

/-- Teschl, §6.3, p. 192: `x` is a periodic point of the flow `Φ` (maximal time intervals `I`)
with **positive** period `T = T(x) = inf {T > 0 | Φ(T, x) = x}`, i.e. `x` lies on a regular
periodic orbit (case (ii) of the book's classification; a fixed point has period `0` and is
excluded). Concretely: `0 < T`, `T ∈ I x`, `Φ(T, x) = x`, and `Φ(t, x) ≠ x` for `0 < t < T`
(so `T` is the least positive return time). This is the standing assumption of §12.1: "a periodic
solution `Φ(t, x₀)` of period `T = T(x₀)`". -/
def IsRegularPeriodicPoint {n : ℕ} (I : (Fin n → ℝ) → Set ℝ) (Φ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) (T : ℝ) : Prop :=
  0 < T ∧ T ∈ I x ∧ Φ T x = x ∧ ∀ t : ℝ, 0 < t → t < T → Φ t x ≠ x

end TeschlODE.PeriodicOrbits



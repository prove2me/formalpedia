-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_IsPiecewiseMonotone
-- name    : KawasakiSOS_Threshold_IsPiecewiseMonotone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:54.219197+00:00
-- url     : https://prove2.me/theorems/b2f729a7-bd72-4a74-8f21-5825143abeea
-- title:
--   Piecewise monotone functions on $[0,1]$
-- statement:
--   A function $f:[0,1]\to\mathbb R$ is piecewise monotone if there is a finite partition $0=t_0<t_1<\dots<t_m=1$ such that on each interval $[t_i,t_{i+1}]$ the function $f$ is nondecreasing or nonincreasing.
--
--   **Formalization Note** Monotonicity is meant in the weak sense, so constant pieces are allowed.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Theorem 4.3, p. 10 (PDF p. 11)

import Mathlib

namespace KawasakiSOS.Threshold

/-- `f` is piecewise monotone on `[0, 1]`: there is a finite partition `0 = t_0 < … < t_m = 1` with `f` monotone or antitone on each piece. Formalization Note: monotonicity is weak, because the profile `F` has flat pieces where `d(i) = 0`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Theorem 4.3, p. 10 (PDF p. 11). -/
def IsPiecewiseMonotone (f : ℝ → ℝ) : Prop :=
  ∃ (m : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧ t m = 1 ∧ (∀ i, i < m → t i < t (i + 1)) ∧
    ∀ i, i < m → MonotoneOn f (Set.Icc (t i) (t (i + 1))) ∨ AntitoneOn f (Set.Icc (t i) (t (i + 1)))

end KawasakiSOS.Threshold



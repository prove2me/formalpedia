-- Prove2me | Definitions.Def_DetTerminalEmbedding1373_Real_Supplement_roundedProjection
-- name    : DetTerminalEmbedding1373_Real_Supplement_roundedProjection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:15:33.222597+00:00
-- url     : https://prove2.me/theorems/c0fedbac-aeed-4042-97a7-6a4d6c7c8c4c
-- title:
--   Rational vectors, admissible radii and the rounded projection $\Pi$ of equation (64)
-- statement:
--   For a rational vector $v\in\mathbb Q^m$ write $\bar v\in\mathbb R^m$ for the same vector in the Euclidean space $E_m$, and $R_v=\sum_{j=1}^m v_j^2$ for its exact squared norm.
--
--   1. **Admissible radius.** Given an accuracy $\xi$, a rational $r_v$ is admissible for $v$ if $r_v=1$ when $R_v\le 1$, and $\sqrt{R_v}\le r_v\le(1+\xi/4)\sqrt{R_v}$ when $R_v>1$.
--   2. **Rounding toward zero.** For an integer $N$ and a rational $a$, $\operatorname{rd}_N(a)=\operatorname{sgn}(a)\,2^{-N}\lfloor 2^N|a|\rfloor$, with $\operatorname{sgn}0=0$; this is the point of the grid $2^{-N}\mathbb Z$ nearest to $a$ on the side of $0$.
--   3. **Rounded projection.** With $y_v=v/r_v$,
--
--   $$\Pi(v)_j=\operatorname{sgn}\bigl((y_v)_j\bigr)\,2^{-N}\bigl\lfloor 2^N|(y_v)_j|\bigr\rfloor,\qquad j\in[m].$$
--
--   $\Pi(v)$ is a rational vector that replaces the exact Euclidean projection onto the unit ball in the finite-precision projected subgradient method of the paper; it depends on the chosen radius $r_v$ and grid exponent $N$.
--
--   **Formalization Note** $N$ is an integer and $2^{-N}$ is an integer power of $2$ in $\mathbb Q$. The choice of $r_v$ and $N$ is left to the algorithm in the paper, so the radius and the exponent are explicit arguments, and the admissibility of the radius is a separate predicate.
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), p. 29, equation (64) and the paragraph before it; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Mathlib
import Definitions.Def_DetTerminalEmbedding1373_Real_geometry

set_option autoImplicit false

namespace DetTerminalEmbedding1373.Real.Supplement

/-- A rational vector `v ∈ ℚᵐ` read as a point of the Euclidean space `ℝᵐ` (coordinatewise cast). -/
noncomputable def toE {m : ℕ} (v : Fin m → ℚ) : E m :=
  WithLp.toLp 2 (fun j => (v j : ℝ))

/-- `R_v = ∑ⱼ vⱼ²`, the exact squared Euclidean norm of a rational vector (p. 29). -/
def sqNorm {m : ℕ} (v : Fin m → ℚ) : ℚ := ∑ j, v j ^ 2

/-- The admissible radii of p. 29 for accuracy `ξ`: if `R_v ≤ 1` then `r_v = 1`; otherwise `r_v`
is a rational upper approximation `√R_v ≤ r_v ≤ (1 + ξ/4) √R_v`. -/
def AdmissibleRadius {m : ℕ} (ξ : ℝ) (v : Fin m → ℚ) (r : ℚ) : Prop :=
  (sqNorm v ≤ 1 → r = 1) ∧
  (1 < sqNorm v →
    Real.sqrt (sqNorm v : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) ≤ (1 + ξ / 4) * Real.sqrt (sqNorm v : ℝ))

/-- Rounding toward zero on the grid `2^{-N} ℤ`: `sgn(a) · 2^{-N} · ⌊2^N |a|⌋`, with `sgn 0 = 0`. -/
def roundTowardZero (N : ℤ) (a : ℚ) : ℚ :=
  ((SignType.sign a : SignType) : ℚ) * (2 : ℚ) ^ (-N) * (⌊(2 : ℚ) ^ N * |a|⌋ : ℚ)

/-- Equation (64), p. 29: the rounded projection `Π(v)ⱼ = sgn((y_v)ⱼ) 2^{-N} ⌊2^N |(y_v)ⱼ|⌋`
with `y_v = v / r_v`, for a chosen radius `r_v` and grid exponent `N`. -/
def roundedProjection {m : ℕ} (v : Fin m → ℚ) (r : ℚ) (N : ℤ) : Fin m → ℚ :=
  fun j => roundTowardZero N (v j / r)

end DetTerminalEmbedding1373.Real.Supplement



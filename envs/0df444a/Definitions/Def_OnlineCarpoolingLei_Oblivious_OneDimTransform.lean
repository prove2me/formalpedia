-- Prove2me | Definitions.Def_OnlineCarpoolingLei_Oblivious_OneDimTransform
-- name    : OnlineCarpoolingLei_Oblivious_OneDimTransform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:13.637861+00:00
-- url     : https://prove2.me/theorems/5a96a638-30a5-4133-9378-8e9b6245c973
-- title:
--   The one-dimensional transform (5.1): $F_g$, $\kappa_g$ and $\Psi_g$
-- statement:
--   For a finite convex function $g:\mathbb R\to[0,\infty)$ define
--   $$F_g(z)=\min_{|s-z|\le2}g(s),\qquad \kappa_g=\min_{|\xi|\le27}\max\{g(\xi-2),g(\xi+2)\},\qquad \Psi_g(z)=\max\{\kappa_g,F_g(z)\}.\tag{5.1}$$
--   Here $F_g$ is the sliding minimum of $g$ over windows of length $4$, $\kappa_g$ is the smallest level whose sublevel set contains an interval of length $4$ centered in $[-27,27]$, and $\Psi_g$ bounds the least value attainable by an allowed move (Lemma 5.1) while its Gaussian average does not exceed that of $g$ (Lemma 5.2).
--
--   **Formalization Note** The minima are written as infima (`sInf`) of the images of the compact intervals $[z-2,z+2]$ and $[-27,27]$. For the convex, hence continuous, $g$ to which they are applied the infima are attained, so they are the minima of (5.1); nonnegativity of $g$ keeps the sets bounded below.
-- source:
--   Yuhao Lei, STOC 2027 submission #416 (October 2026), Section 5, (5.1), p.10 (PDF p.10)

import Mathlib

/-!
Yuhao Lei, *Online carpooling against an oblivious adversary*, STOC 2027 submission #416
(October 2026), §5 (p.10), display (5.1): the sliding minimum `F_g`, the level `κ_g` and the
transform `Ψ_g` of a function `g : ℝ → ℝ`.

For the finite convex nonnegative `g` of §5 these infima are attained minima (`g` is
continuous and the index sets are nonempty compact intervals); `g ≥ 0` makes every set
bounded below, so `sInf` is the true infimum.
-/

namespace OnlineCarpoolingLei.Oblivious

/-- `F_g(z) = min_{|s − z| ≤ 2} g(s)`. -/
noncomputable def slideMin (g : ℝ → ℝ) (z : ℝ) : ℝ := sInf (g '' Set.Icc (z - 2) (z + 2))

/-- (5.1) `κ_g = min_{|ξ| ≤ 27} max {g(ξ − 2), g(ξ + 2)}`. -/
noncomputable def kappa (g : ℝ → ℝ) : ℝ :=
  sInf ((fun ξ => max (g (ξ - 2)) (g (ξ + 2))) '' Set.Icc (-27 : ℝ) 27)

/-- `Ψ_g(z) = max {κ_g, F_g(z)}`. -/
noncomputable def psi1 (g : ℝ → ℝ) (z : ℝ) : ℝ := max (kappa g) (slideMin g z)

end OnlineCarpoolingLei.Oblivious



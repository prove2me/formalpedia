-- Prove2me | Definitions.Def_HOTrap_interpolant
-- name    : HOTrap_interpolant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:03.304365+00:00
-- url     : https://prove2.me/theorems/a2073e67-64dd-4d76-99b3-324500113bf8
-- title:
--   Componentwise interpolant $I=\sum_i\tilde F_i\ell_i$
-- statement:
--   The componentwise interpolant of supplied values $\tilde F_i$ is
--   $$
--   I(y):=\sum_{i=1}^n\tilde F_i\,\ell_i(y).
--   $$
--
--   It is the reconstruction of Lemma A.4 and Proposition A.5.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, p.54

import Mathlib

namespace HOTrap

/-- **The componentwise interpolant** `I(y) := ∑ᵢ F̃ᵢ ℓᵢ(y)` of supplied values `F̃ᵢ`. Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, p.54. -/
noncomputable def interpolant {d : ℕ} {ι : Type*} [Fintype ι] {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (ℓ : ι → EuclideanSpace ℝ (Fin d) → ℝ) (v : ι → G) : EuclideanSpace ℝ (Fin d) → G :=
  fun y => ∑ i, ℓ i y • v i

end HOTrap



-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsPolyhedronW
-- name    : DiscreteConvex_ConjugacyDualityB_IsPolyhedronW
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:27:44.404512+00:00
-- url     : https://prove2.me/theorems/b7031d90-02f6-409e-a5fc-3bf67ed96309
-- title:
--   A polyhedron in a real coordinate space
-- statement:
--   A subset of $\mathbb{R}^W$ cut out by finitely many linear inequalities: $S=\{x : \sum_w a_i(w)x(w)\le b_i \text{ for all } i\}$ for some finite family $(a_i,b_i)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §8.1

import Mathlib

namespace DiscreteConvex.ConjugacyDualityB

/-- A subset of `Rᵂ` cut out by finitely many linear inequalities. -/
def IsPolyhedronW {W : Type*} [Fintype W] (S : Set (W → ℝ)) : Prop :=
  ∃ (m : ℕ) (a : Fin m → W → ℝ) (b : Fin m → ℝ), S = {x | ∀ i, ∑ w, a i w * x w ≤ b i}

end DiscreteConvex.ConjugacyDualityB



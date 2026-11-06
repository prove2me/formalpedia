-- Prove2me | Definitions.Def_HOTrap_CkNear
-- name    : HOTrap_CkNear
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:45:57.917869+00:00
-- url     : https://prove2.me/theorems/24b8634c-bd6a-42b4-9e75-bfd2521cb706
-- title:
--   $F$ is $C^k$ on a neighbourhood of $S$
-- statement:
--   $F$ is $k$ times continuously differentiable on a neighbourhood of $S$: there is an open set $U\supseteq S$ on which $F$ is $C^k$.
--
--   This is the regularity hypothesis of Lemmas 3.9, A.4 and A.7.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Lemma 3.9, p.17; Lemma A.4, p.55; Lemma A.7, p.61

import Mathlib

namespace HOTrap

/-- **`F` is `C^k` on a neighbourhood of `S`.** Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Lemma 3.9, p.17; Lemma A.4, p.55;
Lemma A.7, p.61.

**Formalization Note** "A neighbourhood of `S`" is an open set `U ⊇ S`. -/
def CkNear {d : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (S : Set (EuclideanSpace ℝ (Fin d))) (k : ℕ) (F : EuclideanSpace ℝ (Fin d) → G) : Prop :=
  ∃ U, IsOpen U ∧ S ⊆ U ∧ ContDiffOn ℝ k F U

end HOTrap



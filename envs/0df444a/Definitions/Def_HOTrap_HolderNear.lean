-- Prove2me | Definitions.Def_HOTrap_HolderNear
-- name    : HOTrap_HolderNear
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:51.176201+00:00
-- url     : https://prove2.me/theorems/a023f211-7ff1-4f00-9efb-b54a2ec6d437
-- title:
--   $F\in C^{p,\beta}(L)$ on a neighbourhood of $S$
-- statement:
--   $F\in C^{p,\beta}(L)$ on a neighbourhood of $S$ means that there is an open set $U\supseteq S$ on which $F\in C^{p,\beta}(L)$.
--
--   The paper states: all regularity assumptions hold on a neighbourhood of $S$.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Appendix A, Notation, p.53

import Mathlib
import Definitions.Def_HOTrap_HolderOn

namespace HOTrap

/-- **`F ∈ C^{p,β}(L)` on a neighbourhood of `S`.** Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Appendix A, Notation, p.53.

**Formalization Note** "A neighbourhood of `S`" is an open set `U ⊇ S`. -/
def HolderNear {d : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (S : Set (EuclideanSpace ℝ (Fin d))) (p : ℕ) (β L : ℝ) (F : EuclideanSpace ℝ (Fin d) → G) : Prop :=
  ∃ U, S ⊆ U ∧ HolderOn U p β L F

end HOTrap



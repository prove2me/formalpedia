-- Prove2me | Definitions.Def_RepellingPairs_IsMetric
-- name    : RepellingPairs_IsMetric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:39.246474+00:00
-- url     : https://prove2.me/theorems/86f0ce79-def9-4377-83ed-c787714d97e5
-- title:
--   Metric on a terminal set
-- statement:
--   A function $D:\{0,\dots,k-1\}^2\to\mathbb R$ is a **metric** if $D(i,i)=0$, $D(i,j)=D(j,i)$, $D(i,j)>0$ for $i\ne j$, and $D(i,l)\le D(i,j)+D(j,l)$.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §1, p.2; §2, p.5

import Mathlib

set_option autoImplicit false

namespace RepellingPairs

/-- `D` is a metric on the terminal set `Fin k`: zero exactly on the diagonal, symmetric, and satisfying
the triangle inequality. Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), §1,
p.2, and §2, p.5 ("a metric D on a terminal set T"). -/
structure IsMetric {k : ℕ} (D : Fin k → Fin k → ℝ) : Prop where
  self : ∀ i, D i i = 0
  symm : ∀ i j, D i j = D j i
  pos : ∀ i j, i ≠ j → 0 < D i j
  triangle : ∀ i j l, D i l ≤ D i j + D j l

end RepellingPairs



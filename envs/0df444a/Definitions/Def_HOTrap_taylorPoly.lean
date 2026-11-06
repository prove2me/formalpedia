-- Prove2me | Definitions.Def_HOTrap_taylorPoly
-- name    : HOTrap_taylorPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:45:57.146212+00:00
-- url     : https://prove2.me/theorems/889ac2e3-7144-4d0a-b79a-8400d382d961
-- title:
--   Degree-$p$ Taylor polynomial $T_p$ of $F$ at $c$
-- statement:
--   The degree-$p$ Taylor polynomial of $F$ at $c$ is
--   $$
--   T_p(y)=\sum_{k=0}^p\frac1{k!}D^kF(c)[y-c,\dots,y-c].
--   $$
--
--   It is the comparison polynomial of Lemmas A.3 and A.4.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Lemma A.3, p.54

import Mathlib

namespace HOTrap

/-- **The degree-`p` Taylor polynomial** `T_p` of `F` at `c`, Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Lemma A.3, p.54:
`T_p(y) = ∑_{k=0}^p (1/k!) D^k F(c)[y − c, …, y − c]`. -/
noncomputable def taylorPoly {d : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : EuclideanSpace ℝ (Fin d) → G) (p : ℕ) (c : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) → G :=
  fun y => ∑ k ∈ Finset.range (p + 1),
    ((k.factorial : ℝ))⁻¹ • iteratedFDeriv ℝ k F c (fun _ => y - c)

end HOTrap



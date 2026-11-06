-- Prove2me | Definitions.Def_HOTrap_IsUnisolvent
-- name    : HOTrap_IsUnisolvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:00.309248+00:00
-- url     : https://prove2.me/theorems/08747c66-2325-4199-bf81-fb8234e4a539
-- title:
--   Unisolvent nodes
-- statement:
--   Nodes $z_1,\dots,z_n$ are unisolvent for a polynomial space $P$ if every assignment of scalar values at the nodes determines a unique polynomial in $P$, that is, if the map $q\mapsto(q(z_i))_i$ from $P$ to $\mathbb R^n$ is bijective.
--
--   This is the condition under which a Lagrange basis exists.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, p.54

import Mathlib

namespace HOTrap

/-- **Unisolvent nodes.** Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, p.54: "every assignment of scalar values at these nodes determines a
unique polynomial in `P`". This is bijectivity of the evaluation map `q ↦ (q(zᵢ))ᵢ`. -/
def IsUnisolvent {d : ℕ} {ι : Type*} (Q : Submodule ℝ (EuclideanSpace ℝ (Fin d) → ℝ)) (z : ι → EuclideanSpace ℝ (Fin d)) : Prop :=
  Function.Bijective (fun (q : Q) (i : ι) => (q : EuclideanSpace ℝ (Fin d) → ℝ) (z i))

end HOTrap



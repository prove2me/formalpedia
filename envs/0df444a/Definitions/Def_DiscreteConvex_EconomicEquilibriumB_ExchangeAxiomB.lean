-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ExchangeAxiomB
-- name    : DiscreteConvex_EconomicEquilibriumB_ExchangeAxiomB
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:43:51.5848+00:00
-- url     : https://prove2.me/theorems/a71f41dc-1532-4914-a606-e99e962c4495
-- title:
--   ExchangeAxiomB
-- statement:
--   Axiom (B-EXC[Z]): $B$ is an M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z]), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.101, axiom (B-EXC[Z]), redeclared

import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- Axiom (B-EXC[Z]): `B` is an M-convex set. -/
def ExchangeAxiomB (B : Set (Option K → ℤ)) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B, ∀ u ∈ Finset.univ.filter (fun v => y v < x v),
    ∃ v ∈ Finset.univ.filter (fun v => x v < y v),
      (fun w => x w - (if w = u then (1:ℤ) else 0) + (if w = v then (1:ℤ) else 0)) ∈ B ∧
      (fun w => y w + (if w = u then (1:ℤ) else 0) - (if w = v then (1:ℤ) else 0)) ∈ B

end DiscreteConvex.EconomicEquilibriumB



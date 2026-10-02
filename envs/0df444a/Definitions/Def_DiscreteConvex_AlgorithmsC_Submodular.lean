-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_Submodular
-- name    : DiscreteConvex_AlgorithmsC_Submodular
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:17:02.4944+00:00
-- url     : https://prove2.me/theorems/d5608504-3141-4096-9afe-753238722e1c
-- title:
--   Submodular
-- statement:
--   A set function $\rho:2^W\to\mathbb Z$ is submodular.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, redeclared, generic ground type.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288, redeclared, generic ground type

import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A set function `ρ : 2^W → Z` is submodular, with `ρ(∅) = 0` — the standing normalization of
Murota, *Discrete Convex Analysis*, SIAM 2003, §10.2.1 (p. 285). -/
def Submodular {W : Type*} [DecidableEq W] (rho : Finset W → ℤ) : Prop :=
  rho ∅ = 0 ∧ ∀ X Y : Finset W, rho X + rho Y ≥ rho (X ∪ Y) + rho (X ∩ Y)

end DiscreteConvex.AlgorithmsC



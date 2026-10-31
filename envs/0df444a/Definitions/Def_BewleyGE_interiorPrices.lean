-- Prove2me | Definitions.Def_BewleyGE_interiorPrices
-- name    : BewleyGE_interiorPrices
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:14.729688+00:00
-- url     : https://prove2.me/theorems/4c6bbf16-b503-4c0d-9d51-e1c2e76d6404
-- title:
--   Interior prices $P$ (equation (3))
-- statement:
--   The set of **interior normalized prices** is
--   $$
--   P=\{(p,r)\in\Lambda : p\gg0,\ r>0\},\tag{3}
--   $$
--   the domain of the excess demand function. On $P$, $r<1$ follows from $p\gg0$.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, (3), p.11 (restated p.20)

import Mathlib
import Definitions.Def_BewleyGE_priceSimplex

namespace BewleyGE

/-- **Interior prices** `P = {(p, r) ∈ Λ : p ≫ 0, r > 0}`, equation (3).
Light, arXiv:1906.06810v2, (3), p.11 (restated p.20).

**Formalization Note.** With `π = (p, r)` as in `priceSimplex`, `p ≫ 0` and `r > 0` say that every
coordinate of `π` is positive. On `P`, `r < 1` follows from `p ≫ 0`. -/
def interiorPrices (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {π | π ∈ priceSimplex n ∧ ∀ k, 0 < π k}

end BewleyGE



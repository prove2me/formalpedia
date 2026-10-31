-- Prove2me | Definitions.Def_NashStackelberg_NASP_cost
-- name    : NashStackelberg_NASP_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:16:55.632358+00:00
-- url     : https://prove2.me/theorems/34dbc62a-48a4-4b10-b668-63e8aee1ab97
-- title:
--   The cost $(c^i)^\top x^i+(C^ix^{-i})^\top x^i$ of a NASP player
-- statement:
--   For a NASP $N$, a player $i$ and a profile $x=(x^1,\dots,x^n)$, player $i$'s cost is
--   $$
--   f^i(x^i,x^{-i})=(c^i)^\top x^i+\Big(\sum_{j\ne i}C^{ij}x^j\Big)^{\!\top}x^i ,
--   $$
--   which player $i$ minimizes. It is linear in $x^i$ for fixed $x^{-i}$ and bilinear in $(x^i,x^j)$. The same cost is used in the convexified game $\widetilde N$.
--
--   **Formalization Note** $C^ix^{-i}$ is written as the sum of the blocks $C^{ij}x^j$ over the other players $j$.
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Definition 4, p.8; Algorithm 1, Step 3, p.12

import Mathlib
import Definitions.Def_NashStackelberg_NASP_Var

open Matrix

namespace NashStackelberg

/-- **The cost of a NASP player** (Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, *When Nash
Meets Stackelberg*, arXiv:1910.06452v6, Definition 4, p.8):
`fⁱ(xⁱ, x⁻ⁱ) = (cⁱ)ᵀ xⁱ + (Cⁱ x⁻ⁱ)ᵀ xⁱ`, minimized by player `i`.

**Formalization Note.** `Cⁱ x⁻ⁱ` is `Σ_{j ≠ i} C i j xʲ` (the blocks of `Cⁱ`). The same cost is
used in the convexified game `Ñ` (p.11, Step 3 of Algorithm 1). -/
def NASP.cost {n : ℕ} (N : NASP n) (i : Fin n) (x : (j : Fin n) → N.Var j → ℝ) : ℝ :=
  N.c i ⬝ᵥ x i + (∑ j ∈ Finset.univ.erase i, N.C i j *ᵥ x j) ⬝ᵥ x i

end NashStackelberg



-- Prove2me | Definitions.Def_MarkovChainChoice_DimReduction_H
-- name    : MarkovChainChoice_DimReduction_H
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T09:24:50.224986+00:00
-- url     : https://prove2.me/theorems/165bc70c-9485-4f4f-b96a-47cc5680726f
-- title:
--   The polyhedron $\mathcal H$ of flow-balance pairs $(x,z)$
-- statement:
--   For a Markov chain choice model $(\lambda,\rho)$, the polyhedron $\mathcal H\subseteq\mathbb R^n\times\mathbb R^n$ consists of all pairs $(x,z)$ with
--   $$
--   x_j\ge 0,\qquad z_j\ge 0,\qquad x_j+z_j=\lambda_j+\sum_{i\in N}\rho_{i,j}z_i\qquad\text{for all } j\in N.
--   $$
--   Every solution $(P_S,R_S)$ of the (Balance) equations lies in $\mathcal H$; the constraints of $\mathcal H$ are the (Balance) equations without the requirement that $x$ vanish off $S$ and $z$ vanish on $S$.
--
--   $\mathcal H$ is the feasible set of the paper's assortment linear program and, together with the capacity rows, of the (Reduced) linear program.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1326, Section 3, definition of the set ℋ

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Model
open MarkovChainChoice.Shared

namespace MarkovChainChoice.DimReduction

/-- The polyhedron `ℋ` (p. 1326): pairs `(x, z) ∈ ℝ^n × ℝ^n` with `x ≥ 0`, `z ≥ 0` and
`x_j + z_j = λ_j + ∑_i ρ_{i,j} z_i` for all `j`. -/
def H {n : ℕ} (M : Model n) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | (∀ j, 0 ≤ p.1 j) ∧ (∀ j, 0 ≤ p.2 j) ∧
    ∀ j, p.1 j + p.2 j = M.lam j + ∑ i, M.rho i j * p.2 i}

end MarkovChainChoice.DimReduction



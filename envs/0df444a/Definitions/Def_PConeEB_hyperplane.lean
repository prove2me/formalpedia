-- Prove2me | Definitions.Def_PConeEB_hyperplane
-- name    : PConeEB_hyperplane
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:12.311478+00:00
-- url     : https://prove2.me/theorems/31c7b96d-ad8c-458c-b107-7b1a6e8b8ce9
-- title:
--   The orthogonal complement $\{z\}^\perp$
-- statement:
--   For $z\in\mathcal E$,
--   $$
--   \{z\}^\perp=\{x\in\mathcal E:\langle x,z\rangle=0\}.
--   $$
--   Exposed faces of a cone $K$ have the form $K\cap\{z\}^\perp$ with $z\in K^*$.
--
--   **Formalization Note** For $z=0$ this set is the whole space, as in the paper.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, §2, p.3

import Mathlib

namespace PConeEB

/-- The orthogonal complement `{z}^⊥ = {x | ⟨x, z⟩ = 0}` of a single vector.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, §2, p.3. -/
def hyperplane {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (z : E) : Set E :=
  {x | inner ℝ x z = 0}

end PConeEB



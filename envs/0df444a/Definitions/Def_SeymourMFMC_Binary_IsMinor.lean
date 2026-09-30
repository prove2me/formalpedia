-- Prove2me | Definitions.Def_SeymourMFMC_Binary_IsMinor
-- name    : SeymourMFMC_Binary_IsMinor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T01:42:49.350355+00:00
-- url     : https://prove2.me/theorems/55e9dbad-3f47-466d-b0e8-49c8ce468d08
-- title:
--   Minor of a clutter: obtained by a sequence of deletions and contractions
-- statement:
--   A clutter $\mathbf L'$ is a **minor** of $\mathbf L$ if it may be obtained from $\mathbf L$ by a finite sequence of deletions $\mathbf L_1 \mapsto \mathbf L_1 \setminus Z$ and contractions $\mathbf L_1 \mapsto \mathbf L_1 / Z$, with arbitrary sets $Z$ at each step. The empty sequence is allowed, so $\mathbf L$ is a minor of itself.
--
--   Minors are the order in which the paper's excluded-minor characterization is stated.
--
--   **Formalization Note** The reflexive–transitive closure (`Relation.ReflTransGen`) of the one-step relation "$\mathbf L_2 = \mathbf L_1 \setminus Z$ or $\mathbf L_2 = \mathbf L_1 / Z$ for some finite set $Z$".
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 194, Section 2

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_deletion
import Definitions.Def_SeymourMFMC_Binary_contraction

namespace SeymourMFMC.Binary

/-- `IsMinor L' L`: `L'` is a **minor** of `L` (Seymour 1977, p. 194), i.e. `L'` may be obtained
from `L` by a finite sequence (possibly empty) of deletions `· \ Z` and contractions `· / Z` of
arbitrary sets `Z`. In particular every clutter is a minor of itself. -/
def IsMinor {α : Type*} [DecidableEq α] (L' L : Finset (Finset α)) : Prop :=
  Relation.ReflTransGen
    (fun L₁ L₂ : Finset (Finset α) => ∃ Z : Finset α, L₂ = deletion L₁ Z ∨ L₂ = contraction L₁ Z)
    L L'

end SeymourMFMC.Binary



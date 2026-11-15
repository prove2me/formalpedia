-- Prove2me | Definitions.Def_StableMSR_DecompositionSearch_Recurrence
-- name    : StableMSR_DecompositionSearch_Recurrence
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-14T17:27:20.475203+00:00
-- url     : https://prove2.me/theorems/3997d106-b492-4e75-84cc-7d17199ac0e4
-- title:
--   Finite tight-block decomposition search
-- statement:
--   The depth-bounded search accepts a block $(S,C)$ at positive depth if a bag of at most $w+1$ vertices contains $S$, lies in $S\cup C$, introduces a vertex of $C$, and each resulting connected component is accepted at smaller depth with its exact external boundary of size at most $w$. Depth zero rejects. Global recognition tests all components of $G$ with empty boundary at depth $|V(G)|$. These finite recurrences express search success and do not assert an instruction-level implementation.
-- source:
--   Finite-state bounded-treewidth decomposition construction supporting the Prove2Me Exact Sum-of-Radii Clustering under Any Constant Stability mission.

import Definitions.Def_StableMSR_TightBlockSearch
namespace StableMSR.Recovery.DecompositionSearch
variable {V : Type} [Fintype V] [DecidableEq V]
noncomputable def accepts (G : SimpleGraph V) (w : ℕ) : ℕ → Finset V → Finset V → Prop
  | 0, _, _ => False
  | m+1, S, C => ∃ B : Finset V,
      S ⊆ B ∧ B ⊆ S ∪ C ∧ B.card ≤ w+1 ∧ (B ∩ C).Nonempty ∧
      ∀ D ∈ children G B C,
        (boundary G D).card ≤ w ∧ accepts G w m (boundary G D) D

noncomputable def recognizes (G : SimpleGraph V) (w : ℕ) : Prop :=
  ∀ C ∈ PartialDecompositions.components G ∅,
    accepts G w (Fintype.card V) ∅ C

end StableMSR.Recovery.DecompositionSearch



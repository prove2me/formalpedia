-- Prove2me | Definitions.Def_VDCyclePack_StructBound
-- name    : VDCyclePack_StructBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:11.964419+00:00
-- url     : https://prove2.me/theorems/eacc4ea3-28f1-49bc-9b4e-438b98df5a26
-- title:
--   The structural hypothesis of Theorem 4.2
-- statement:
--   For a family $S$ of cycles and reals $\alpha,\gamma$, the **structural bound** says that every subfamily $R\subseteq S$, with $t=|R|$, satisfies
--   $$
--   \beta\Bigl(\bigcup_{C\in R}C\Bigr)\le \alpha t+\gamma t\log_2(t+2).
--   $$
--
--   It is the hypothesis of the rounding theorem; Lemma 4.3 provides it for the candidate family.
--
--   **Formalization Note** Every subfamily is quantified, including $\emptyset$ and $S$ (p.12). The union is the supremum in the subgraph lattice.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Theorem 4.2, p.12

import Mathlib
import Definitions.Def_VDCyclePack_cycleRank

namespace VDCyclePack

/-- **The structural hypothesis of Theorem 4.2.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Theorem 4.2, p.12: "Let α, γ ≥ 0 be such that every R ⊆ S with t = |R| satisfies
β(⋃_{C∈R} C) ≤ αt + γt log(t + 2)."

`StructBound S α γ` says that for every subfamily `R ⊆ S`, with `t = |R|`, the cycle rank of the
union of the members of `R` is at most `α·t + γ·t·log₂(t + 2)`.

**Formalization Note.** Every subfamily is quantified, including `∅` and `S` (p.12: "Requiring
the bound for every subfamily ensures that it continues to apply as cycles are discarded"). The
union is `R.sup id`; logarithms are base two. -/
def StructBound {V : Type*} [Fintype V] {G : SimpleGraph V} (S : Finset G.Subgraph) (α γ : ℝ) :
    Prop :=
  ∀ R ⊆ S, (cycleRank (R.sup id) : ℝ) ≤ α * R.card + γ * R.card * Real.logb 2 (R.card + 2)

end VDCyclePack



-- Prove2me | Definitions.Def_DilatableEntropy_gamma
-- name    : DilatableEntropy_gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:50:46.452366+00:00
-- url     : https://prove2.me/theorems/7e359771-465d-4065-bb1e-06a6277d81fe
-- title:
--   Weights $\gamma_j$ of the dilatable global entropy, (8)
-- statement:
--   The weights $\gamma_j$ ($j\in J$) are defined recursively, from the leaves of the tree up, by
--   $$
--   \gamma_j:=1+\max_{a\in A_j}\ \sum_{j'\in\mathcal C_{ja}}\gamma_{j'} .
--   $$
--   At a decision point with no successors $\gamma_j=1$. The recursion has no factor $2$, unlike the weights of Kroer et al., so $\gamma_j$ grows only linearly with the size of the subtree.
--
--   **Formalization Note** Defined by well-founded recursion on the child relation of the problem; the maximum over the nonempty finite set $A_j$ is a finite supremum.
-- source:
--   Farina, Kroer, Sandholm, Better Regularization for Sequential Decision Spaces, arXiv:2105.12954v2, Definition 4, eq. (8), p.10

import Mathlib
import Definitions.Def_DilatableEntropy_children

namespace DilatableEntropy

/-- The weights `γ_j` of the dilatable global entropy (Farina, Kroer, Sandholm, *Better Regularization for Sequential Decision Spaces*, arXiv:2105.12954v2, Definition 4, eq. (8), p.10),
defined recursively bottom-up over the tree of decision points:
`γ_j := 1 + max_{a ∈ A_j} ∑_{j' ∈ C_{ja}} γ_{j'}`.

**Formalization Note** The recursion is `WellFounded.fix` on the well-founded child relation of
the problem; the maximum over the nonempty finite set `A_j` is `Finset.sup'`. -/
noncomputable def gamma (P : SeqDecisionProblem) : P.J → ℝ :=
  P.wf.fix fun j IH =>
    1 + Finset.univ.sup' Finset.univ_nonempty fun a : P.A j =>
      ∑ j' ∈ (children P (some ⟨j, a⟩)).attach,
        IH j'.1 ⟨a, (Finset.mem_filter.1 j'.2).2⟩

end DilatableEntropy



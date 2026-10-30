-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_IsMatroid
-- name    : SeqPostedPricing_MatroidSPM_IsMatroid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:35:21.652994+00:00
-- url     : https://prove2.me/theorems/12add780-e76d-46b4-aa97-363c4a3e2b87
-- title:
--   Matroid set system (heredity and augmentation)
-- statement:
--   A set system $\mathcal J\subseteq 2^{[n]}$ is a **matroid** if
--
--   1. (heredity) for every $A\in\mathcal J$ and $B\subseteq A$, $B\in\mathcal J$;
--   2. (augmentation) for every $A,B\in\mathcal J$ with $|A|>|B|$ there is $e\in A\setminus B$ with $B\cup\{e\}\in\mathcal J$.
--
--   Theorem 5 is about feasibility constraints of this kind (for example $k$-unit auctions).
--
--   **Formalization Note** The paper's "$B\subset A$" is read as $B\subseteq A$. Exactly the two axioms: $\emptyset\in\mathcal J$ is not required.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4.1, unnumbered, p. 6

import Mathlib

namespace SeqPostedPricing.MatroidSPM

/-- **Matroid set system.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §4.1, unnumbered, p. 6 (PDF p. 8): "1. (heredity) For every A ∈ J, B ⊂ A implies B ∈ J.
2. (augmentation) For every A, B ∈ J with |A| > |B|, there exists e ∈ A \ B such that B ∪ {e}
∈ J."

`IsMatroid Feas`: the family `J = {A | Feas A}` of subsets of the agents `Fin n` is hereditary
and has the augmentation property.

**Formalization Note.** "B ⊂ A" is read as `B ⊆ A` (for `B = A` the conclusion is the
hypothesis). Exactly the paper's two axioms: `Feas ∅` is not required (it follows from heredity
as soon as some set is feasible). Mathlib's bundled `Matroid` is not used. -/
def IsMatroid {n : ℕ} (Feas : Finset (Fin n) → Prop) : Prop :=
  (∀ A B : Finset (Fin n), Feas A → B ⊆ A → Feas B) ∧
    (∀ A B : Finset (Fin n), Feas A → Feas B → B.card < A.card →
      ∃ e ∈ A \ B, Feas (insert e B))

end SeqPostedPricing.MatroidSPM



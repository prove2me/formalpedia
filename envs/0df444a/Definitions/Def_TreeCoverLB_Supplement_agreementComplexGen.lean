-- Prove2me | Definitions.Def_TreeCoverLB_Supplement_agreementComplexGen
-- name    : TreeCoverLB_Supplement_agreementComplexGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:22:42.921204+00:00
-- url     : https://prove2.me/theorems/5cda8b5c-e593-4489-92f9-44c5cd8605d0
-- title:
--   The agreement complex $I(A_1,\dots,A_k)$ over general alphabets
-- statement:
--   Let $k\ge 1$ and let $A_1,\dots,A_k$ be finite alphabets. Two words $x,y\in\prod_{i=1}^k A_i$ **agree** if $x_i=y_i$ for some coordinate $i\in[k]$. The **agreement complex** is the abstract simplicial complex on the vertex set $\prod_{i=1}^k A_i$ whose faces are the pairwise agreeing families of words:
--   $$
--   I(A_1,\dots,A_k)=\Big\{\sigma\subseteq\prod_{i=1}^k A_i\;:\;\forall x,y\in\sigma\ \exists i\in[k],\ x_i=y_i\Big\}.
--   $$
--
--   For $A_1=\dots=A_k=\mathbb Z_p$ this is the complex $I_{p,k}$ of the main mission. The general version is the space $X=|I(A_1,\dots,A_k)|$ of Theorem 7.2, where the alphabets encode an arbitrary labelling method for the $k$ trees.
--
--   **Formalization Note** The alphabets are a family `A : Fin k → Type*` and words are dependent functions `∀ i, A i`. Definition 4.1 also asks the alphabets to be nonempty and finite. The theorems that use this complex carry those conditions as hypotheses; the definition does not. With `A i = ZMod p` the definition is literally the published `TreeCoverLB.agreementComplex p k` (the two are equal by `rfl`).
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Definition 4.1, p.11 (PDF p.13)

import Mathlib

namespace TreeCoverLB.Supplement

/-- The **agreement complex** `I(A_1, …, A_k)` over general alphabets (Chen, Huang, Tan, Xu,
*Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026),
Definition 4.1, p.11 (PDF p.13)): the vertices are the words `x ∈ ∏_{i=1}^k A_i`, and a finite
family `σ` of words is a face iff any two words `x, y ∈ σ` agree, i.e. `x_i = y_i` for some
coordinate `i ∈ [k]`.

**Formalization Note** The alphabets are a family `A : Fin k → Type*` and words are dependent
functions `∀ i, A i`. Definition 4.1 asks the alphabets to be nonempty and finite; those
conditions are carried as hypotheses (`Fintype (A i)`, `Nonempty (A i)`) by the statements that
use this complex, not by the definition. For `A i = ZMod p` this is literally the published
`TreeCoverLB.agreementComplex p k` (`I_{p,k}`). -/
def agreementComplexGen {k : ℕ} (A : Fin k → Type*) : Set (Finset (∀ i, A i)) :=
  {σ | ∀ x ∈ σ, ∀ y ∈ σ, ∃ i, x i = y i}

end TreeCoverLB.Supplement



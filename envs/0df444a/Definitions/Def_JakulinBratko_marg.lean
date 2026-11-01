-- Prove2me | Definitions.Def_JakulinBratko_marg
-- name    : JakulinBratko_marg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:00:43.77837+00:00
-- url     : https://prove2.me/theorems/a3ea6eef-e98e-47c7-8ece-7adf637f14ad
-- title:
--   Eq. (8) — marginal distribution of a subset of attributes
-- statement:
--   For a subset $\mathcal S\subseteq\mathcal A$ of the attributes and an assignment $\mathbf s$ of values to the attributes in $\mathcal S$, the marginal probability is
--
--   $$
--   P(\mathbf s)=\sum_{\substack{\mathbf a\in\Re_{\mathcal A}\\ \mathbf a|_{\mathcal S}=\mathbf s}}P(\mathbf a).
--   $$
--
--   For $\mathcal S=\emptyset$ there is exactly one assignment, and its mass is the total mass of $P$.
--
--   **Formalization Note** An assignment of $\mathcal S$ is a dependent function on the subtype of elements of the `Finset`, and the condition on $\mathbf a$ is `S.restrict a = s`.
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.4, Eq. (8), p.8

import Mathlib

namespace JakulinBratko

/-- The marginal distribution `P(𝐬)` of a subset `S` of the attributes, Eq. (8), p.8
(Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3): the sum of `P(𝐚)` over all full assignments `𝐚` that agree with `𝐬` on `S`.

**Formalization Note.** An assignment of the attributes in `S` is a dependent function on the
subtype `↥S`, and `S.restrict a` is the restriction of `a` to `S`. For `S = ∅` there is one
assignment, whose mass is the total mass of `P`. -/
def marg {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (S : Finset ι) (s : ∀ i : S, α i) : ℝ :=
  ∑ a with S.restrict a = s, P a

end JakulinBratko



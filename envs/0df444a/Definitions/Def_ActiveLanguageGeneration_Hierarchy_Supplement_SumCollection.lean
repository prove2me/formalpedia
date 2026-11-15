-- Prove2me | Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_SumCollection
-- name    : ActiveLanguageGeneration_Hierarchy_Supplement_SumCollection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:22:02.040672+00:00
-- url     : https://prove2.me/theorems/4c633b6a-c3b9-4796-8eda-928fc3a99749
-- title:
--   The sum-configuration collection C_k
-- statement:
--   For an integer $k\ge2$, over the universe $\mathbb N=\{1,2,\ldots\}$ of positive integers, let
--
--   $$
--   C_k=\Bigl\{L\subseteq\mathbb N:\ |L|=\infty \text{ and there exist distinct } y_1,\ldots,y_k,y_{k+1}\in L \text{ with } \sum_{i=1}^k y_i=y_{k+1}\Bigr\}.
--   $$
--
--   This is the collection separating active $k$-generation from active $(k-1)$-generation with repetition in Appendix B.
--
--   **Formalization Note** The universe is `ℕ+`; the $k+1$ distinct elements are an injective map `Fin (k+1) → ℕ+`, the last coordinate being $y_{k+1}$. The sum is computed after casting to `ℕ`, since `ℕ+` has no zero. The definition makes sense for every $k$; the lemmas use $k\ge2$.
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, collection C_k before Lemma B.5, printed p.28 (PDF p.29); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Language

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- The collection `C_k` of Appendix B, printed p.28 (PDF p.29), over the universe of positive
integers: all infinite `L ⊆ ℕ+` containing `k + 1` pairwise distinct elements
`y₁, …, y_k, y_{k+1}` with `y₁ + ⋯ + y_k = y_{k+1}`
(the sum is computed in `ℕ`, since `ℕ+` has no zero). -/
def sumCollection (k : ℕ) : LanguageCollection ℕ+ :=
  {L | ∃ y : Fin (k + 1) → ℕ+, Function.Injective y ∧ (∀ i, y i ∈ L.val) ∧
    ∑ i : Fin k, (y i.castSucc : ℕ) = (y (Fin.last k) : ℕ)}

end ActiveLanguageGeneration.Hierarchy.Supplement



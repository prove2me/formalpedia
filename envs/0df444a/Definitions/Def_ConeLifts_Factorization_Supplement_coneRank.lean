-- Prove2me | Definitions.Def_ConeLifts_Factorization_Supplement_coneRank
-- name    : ConeLifts_Factorization_Supplement_coneRank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:43:38.403729+00:00
-- url     : https://prove2.me/theorems/5e6abc3b-de81-4bdf-a2b2-e5a2493f1fd1
-- title:
--   $\mathcal K$-rank of a nonnegative matrix and of a convex body
-- statement:
--   Let $\mathcal K = (K_i)_{i \in \mathbb N}$ be a cone family.
--
--   1. The **$\mathcal K$-rank** of a nonnegative matrix $M$, $\operatorname{rank}_{\mathcal K}(M)$, is the smallest $i$ such that $M$ has a $K_i$-factorization (vectors $a^r \in K_i$ for the rows and $b^s \in K_i^*$ for the columns with $\langle a^r, b^s\rangle = M_{rs}$), and $+\infty$ if no such $i$ exists.
--   2. The **$\mathcal K$-rank** of a convex body $C \subseteq \mathbb R^n$ is
--
--   $$
--   \operatorname{rank}_{\mathcal K}(C) = \min\{\, i : \text{the slack operator } S_C \text{ has a } K_i\text{-factorization} \,\},
--   $$
--
--   and $\operatorname{rank}_{\mathcal K}(C) = +\infty$ if no such $i$ exists. For the orthants these are the nonnegative ranks, for the positive semidefinite cones the psd ranks.
--
--   **Formalization Note** Both values lie in `ℕ∞`, with `⊤` for $+\infty$. The matrix rank (`matrixConeRank`) is defined for every real matrix with arbitrary row and column index types; only nonnegative matrices can have a finite rank.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 13, Definition 4.3

import Mathlib
import Definitions.Def_ConeLifts_Factorization_SlackFactorizable
import Definitions.Def_ConeLifts_StableSet_HasConeFactorization
import Definitions.Def_ConeLifts_Factorization_Supplement_ConeFamily

namespace ConeLifts.Factorization.Supplement

/-- The **`𝒦`-rank of a nonnegative matrix** `M` (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2,
Definition 4.3 (1), p. 13): the smallest `i` such that `M` has a `Kᵢ`-factorization
(Definition 3.2, `ConeLifts.StableSet.HasConeFactorization`), and `+∞` (`⊤ : ℕ∞`) if no such `i`
exists. Rows and columns are indexed by arbitrary types; the paper applies the notion to
nonnegative matrices, which are the only ones that can have a factorization through a cone and
its dual with nonnegative pairings. -/
noncomputable def matrixConeRank {ι κ : Type*} (𝒦 : ConeFamily) (M : Matrix ι κ ℝ) : ℕ∞ :=
  ⨅ (i : ℕ) (_ : ConeLifts.StableSet.HasConeFactorization (𝒦.cone i) M), (i : ℕ∞)

/-- The **`𝒦`-rank of a convex body** `C ⊆ ℝⁿ` (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2,
Definition 4.3 (2), p. 13): the smallest `i` such that the slack operator `S_C` has a
`Kᵢ`-factorization (Definition 2.2), and `+∞` (`⊤ : ℕ∞`) if no such `i` exists. -/
noncomputable def coneRank {n : ℕ} (𝒦 : ConeFamily) (C : Set (EuclideanSpace ℝ (Fin n))) : ℕ∞ :=
  ⨅ (i : ℕ) (_ : ConeLifts.Factorization.SlackFactorizable (𝒦.cone i) C), (i : ℕ∞)

end ConeLifts.Factorization.Supplement



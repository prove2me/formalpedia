-- Prove2me | Definitions.Def_ConeLifts_NonnegRank_HasBooleanFactorization
-- name    : ConeLifts_NonnegRank_HasBooleanFactorization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:11:44.25702+00:00
-- url     : https://prove2.me/theorems/9ee8936e-4222-471e-b833-cc3a55349ce3
-- title:
--   Boolean factorization of $\operatorname{supp}(S_C)$ of intermediate dimension $k$
-- statement:
--   The **support** $\operatorname{supp}(S_C)$ of the slack operator of $C$ is the $0/1$ matrix indexed by $\operatorname{ext}(C) \times \operatorname{ext}(C^\circ)$ with a one exactly at the entries where $S_C(x, y) = 1 - \langle x, y\rangle \neq 0$. A **Boolean factorization of $\operatorname{supp}(S_C)$ of intermediate dimension $k$** is a factorization $\operatorname{supp}(S_C) = AB$ with $A \in \{0,1\}^{\operatorname{ext}(C) \times k}$ and $B \in \{0,1\}^{k \times \operatorname{ext}(C^\circ)}$, in Boolean arithmetic ($1 + 1 = 1$).
--
--   Identifying the row $A(x)$ and the column $B(y)$ with subsets of $[k] = \{1, \dots, k\}$, this says: for all $x \in \operatorname{ext}(C)$ and $y \in \operatorname{ext}(C^\circ)$,
--
--   $$1 - \langle x, y\rangle \neq 0 \iff A(x) \cap B(y) \neq \emptyset .$$
--
--   The least such $k$ is the Boolean rank $\operatorname{rank}_B(S_C)$, also called the rectangle covering number of the support.
--
--   **Formalization Note** Rows and columns are encoded as maps $\mathbb{R}^n \to$ `Finset (Fin k)`, constrained only on the extreme points; this is the identification of subsets of $[k]$ with incidence vectors used in the proof of Theorem 4.11.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 15, Definition 4.10 and Theorem 4.11 (support, Boolean factorization of supp(S_C))

import Mathlib
import Definitions.Def_ConeLifts_Shared_polar
import Definitions.Def_ConeLifts_NonnegRank_slackOperator

namespace ConeLifts.NonnegRank

/-- A **Boolean factorization of `supp(S_C)` of intermediate dimension `k`** (Gouveia, Parrilo &
Thomas, arXiv:1111.3164v2, Definition 4.10 and Theorem 4.11, p. 15). `supp(S_C)` is the 0/1 matrix
with a one exactly where `S_C(x, y) ≠ 0`; a Boolean factorization `supp(S_C) = AB` with
`A ∈ {0,1}^{ext(C) × k}`, `B ∈ {0,1}^{k × ext(C°)}` in Boolean arithmetic is encoded, as in the proof
of Theorem 4.11, by the row `A x ⊆ [k]` and the column `B y ⊆ [k]` as subsets of `Fin k`: the
Boolean product entry is one iff `A x ∩ B y ≠ ∅`. -/
def HasBooleanFactorization {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Prop :=
  ∃ A B : EuclideanSpace ℝ (Fin n) → Finset (Fin k),
    ∀ x ∈ Set.extremePoints ℝ C, ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C),
      (slackOperator x y ≠ 0 ↔ (A x ∩ B y).Nonempty)

end ConeLifts.NonnegRank



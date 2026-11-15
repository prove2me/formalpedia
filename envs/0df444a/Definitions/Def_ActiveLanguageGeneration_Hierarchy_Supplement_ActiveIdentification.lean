-- Prove2me | Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_ActiveIdentification
-- name    : ActiveLanguageGeneration_Hierarchy_Supplement_ActiveIdentification
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:21:08.042959+00:00
-- url     : https://prove2.me/theorems/2d450f18-0962-4aad-93a1-3afd2c0264d9
-- title:
--   Active k-identification of an indexed collection
-- statement:
--   Let $C=\{L_1,L_2,\ldots\}$ be a countable collection of infinite languages over $U$, given with an explicit indexing (repetitions in the indexing allowed). An identifier is a map $G:U^\star\to\mathbb N$ from finite histories to indices. For a positive integer $k$, $G$ **actively $k$-identifies** $C$ if for every language $K$ of the collection there is a full, repetition-free enumeration $x_1,x_2,\ldots$ of $K$ such that
--
--   $$
--   L_{G(x_1,\ldots,x_t)}=K\qquad\text{for all } t\ge k .
--   $$
--
--   The output need only be *some* index of the target. $C$ is actively $k$-identifiable if such a $G$ exists. This is the identification analogue of active $k$-generation used in Appendix C.
--
--   **Formalization Note** The indexing is a function `Ls : ℕ → Language U` starting at $0$ (the paper starts at $1$); identifier outputs are natural numbers. Stream index $n$ is time $t=n+1$. Thresholds are positive.
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Definition C.1, printed p.34 (PDF p.35); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Language

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Definition C.1, printed p.34 (PDF p.35): active `k`-identification of an explicitly
indexed collection `C = {Ls 0, Ls 1, …}` (the paper indexes from 1). An identifier maps a
finite history (oldest first) to an index. For every language of the collection there must be
a full injective enumeration on which, at every time `t = n + 1 ≥ k`, the output is *some*
index `j` with `Ls j` equal to the target (not necessarily the index used to name it).
Only positive thresholds are in the paper's domain. -/
def ActiveKIdentifiable {U : Type} (Ls : ℕ → Language U) (k : ℕ) : Prop :=
  0 < k ∧ ∃ G : List U → ℕ, ∀ i : ℕ, ∃ x : ℕ → U, IsEnumeration (Ls i) x ∧
    ∀ n : ℕ, k ≤ n + 1 → Ls (G (inputHistory x n)) = Ls i

end ActiveLanguageGeneration.Hierarchy.Supplement



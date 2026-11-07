-- Prove2me | Definitions.Def_KarpLiptonOM_Alt
-- name    : KarpLiptonOM_Alt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:16.055203+00:00
-- url     : https://prove2.me/theorems/01fa33f5-edb4-4959-b5b7-b6450a528ab5
-- title:
--   Alternating quantifiers $\exists y_1 \forall y_2 \cdots$ over $\{0,1\}^m$
-- statement:
--   For $m, k \in \mathbb N$ and a predicate $V$ on $k$-tuples of strings, the alternating quantification starting with $\exists$ is
--   $$
--   \exists y_1 \, \forall y_2 \, \exists y_3 \cdots Q_k y_k \; V(y_1, \dots, y_k), \qquad y_i \in \{0,1\}^m ,
--   $$
--   and the one starting with $\forall$ is defined symmetrically. It is the quantifier prefix of the levels of the polynomial hierarchy.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.3, p.23 (Σ₂^P, Π₂^P; standard)

import Mathlib

namespace KarpLiptonOM

/-- Alternating quantification over strings of length `m`: `Alt m k true V` is
`∃y₁ ∀y₂ ∃y₃ ⋯ V(y₁, …, y_k)` (and `Alt m k false V` starts with `∀`), every `yᵢ` ranging over
`{0,1}^m` (used for `Σ_k^P`, which Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b) uses without definition; §A.2.3, p.23, "OMIN ⊆ Σ₂^P ∩ Π₂^P"). -/
def Alt (m : ℕ) : ℕ → Bool → (List (List Bool) → Prop) → Prop
  | 0, _, V => V []
  | k + 1, true, V => ∃ y : List Bool, y.length = m ∧ Alt m k false (fun ys => V (y :: ys))
  | k + 1, false, V => ∀ y : List Bool, y.length = m → Alt m k true (fun ys => V (y :: ys))

end KarpLiptonOM



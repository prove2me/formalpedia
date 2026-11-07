-- Prove2me | Definitions.Def_KarpLiptonOM_ONP2
-- name    : KarpLiptonOM_ONP2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:56.860009+00:00
-- url     : https://prove2.me/theorems/bfc2ec25-a3f9-474a-9246-220aab11100b
-- title:
--   A language of pairs in ONP
-- statement:
--   A language of pairs $S \subseteq \{0,1\}^* \times \{0,1\}^*$ (testers $T$ are such languages) is in $\mathrm{ONP}$ if there are a polynomial $p$, a polynomial-time predicate $V(u, a, w)$ and oblivious witnesses $w_{m_1, m_2} \in \{0,1\}^{p(m_1 + m_2)}$ such that for all $u, a$:
--   1. if $(u, a) \in S$, then $V(u, a, w_{|u|, |a|}) = 1$;
--   2. if $(u, a) \notin S$, then $V(u, a, w) = 0$ for every $w$ of length $p(|u| + |a|)$.
--
--   This is Definition A.2.3 for the language of encoded pairs: the paper encodes pairs length-regularly, so the length of the encoding of $(u, a)$ determines $|u|$ and $|a|$, and an oblivious witness per input length is a witness per pair of lengths.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Definition A.2.3, p.21; pair encoding §A.2.1, p.20

import Mathlib
import Definitions.Def_KarpLiptonOM_PolyPred3

namespace KarpLiptonOM

/-- A **language of pairs** `S(u, a)` is in ONP (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), Definition A.2.3, p.21, applied to pairs
encoded length-regularly as in §A.2.1, p.20): a polynomial `p`, a polynomial-time `V(u, a, w)` and
oblivious witnesses `w_{m₁,m₂} ∈ {0,1}^{p(m₁+m₂)}` depending only on `(|u|, |a|)`, with
`S(u, a) → V(u, a, w_{|u|,|a|})` and `¬S(u, a) → ∀ w, ¬V(u, a, w)`.

**Formalization Note** With a length-regular pair encoding, the length of `(u, a)` determines
`|u|` and `|a|`, so a witness per encoded length is a witness per pair of lengths. -/
def ONP2 (S : List Bool → List Bool → Prop) : Prop :=
  ∃ (p : Polynomial ℕ) (V : List Bool → List Bool → List Bool → Prop) (w : ℕ → ℕ → List Bool),
    PolyPred3 V ∧ (∀ m₁ m₂, (w m₁ m₂).length = p.eval (m₁ + m₂)) ∧ ∀ u a : List Bool,
      (S u a → V u a (w u.length a.length)) ∧
      (¬ S u a → ∀ w' : List Bool, w'.length = p.eval (u.length + a.length) → ¬ V u a w')

end KarpLiptonOM



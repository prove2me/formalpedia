-- Prove2me | Definitions.Def_FanInSemigroup_wordLanguage
-- name    : FanInSemigroup_wordLanguage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:46.570094+00:00
-- url     : https://prove2.me/theorems/99c62db3-37cd-4ad0-b7fd-c5a7b05c7289
-- title:
--   The language $L(S,a)$
-- statement:
--   For an element $a$ of a semigroup $S$, the language $L(S,a)$ consists of the nonempty words over the alphabet $S$ whose product in the semigroup is $a$:
--
--   $$
--   L(S,a)=\{a_0a_1\cdots a_l\in S^{+} : a_0a_1\cdots a_l=a\text{ in the semigroup}\}.
--   $$
--
--   These languages connect the product of a semigroup to automata and regular sets.
--
--   **Formalization Note** The page uses a copy $S^\Sigma$ of $S$ as alphabet; here the letters are the elements of $S$ themselves. The empty word is never in $L(S,a)$: the page's automaton is then in its start state $\varepsilon$, which is not an element of $S$.
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, §2, pp.54–55

import Definitions.Def_FanInSemigroup_wordProd

set_option autoImplicit false

namespace FanInSemigroup

/-- The set `L(S,a)` of Chandra, Fortune, Lipton, STOC 1983, pp.54–55: the words over the alphabet
`S` whose product in the semigroup is `a`; "the set {w^Σ ∈ (S^Σ)* : w = a in the semigroup} … is
denoted L(S,a)".

**Formalization Note.** The page's `S^Σ` is a copy of `S` used as letters; here the letters are
the elements of `S` themselves. A semigroup has no empty product, and the page's automaton on the
empty word is in the state `ε`, which is not an element of `S`, so the empty word is not in
`L(S,a)`. -/
def wordLanguage {S : Type*} [Semigroup S] (a : S) : Language S :=
  {w | ∃ (a₀ : S) (l : List S), w = a₀ :: l ∧ wordProd a₀ l = a}

end FanInSemigroup



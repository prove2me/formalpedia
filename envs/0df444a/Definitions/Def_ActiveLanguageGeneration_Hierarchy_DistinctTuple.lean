-- Prove2me | Definitions.Def_ActiveLanguageGeneration_Hierarchy_DistinctTuple
-- name    : ActiveLanguageGeneration_Hierarchy_DistinctTuple
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T21:15:54.840193+00:00
-- url     : https://prove2.me/theorems/cc49e26b-ca57-468a-902a-e0b79c0c3b14
-- title:
--   Ordered distinct tuples and their underlying sets
-- statement:
--   For a subset $X$ of a universe $U$ and a nonnegative integer $r$, let $X_{\ne}^{r}$ be the set of ordered $r$-tuples of pairwise distinct elements of $X$. For $a=(a_1,\ldots,a_r)$ write
--
--   $$
--   \operatorname{tupleValues}(a)=\{a_1,\ldots,a_r\}\subseteq X.
--   $$
--
--   This is the tuple domain used in Lemma 3.3. Order is retained in $a$, while the underlying set is used to specify which outputs are excluded by the free-subset property.
--
--   **Formalization Note** An ordered distinct tuple is an embedding from $\operatorname{Fin}(r)$ into the subtype $X$; its underlying set is the range after forgetting the subtype. The free-set lemma restricts all arities to positive integers, exactly as in the source. At $r=0$ the tuple type contains the empty tuple and its underlying set is empty; no theorem uses zero arity.
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, §3.1.2 immediately before Lemma 3.3, printed p.7 (PDF p.8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Mathlib

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy

/-- The domain `X_{≠}^r` immediately before Lemma 3.3 (printed p.7):
ordered distinct `r`-tuples in `X`, represented by embeddings into its subtype. -/
abbrev DistinctTuple {U : Type} (X : Set U) (r : ℕ) := Fin r ↪ X

/-- The underlying set of entries of an ordered distinct tuple. -/
def tupleValues {U : Type} {X : Set U} {r : ℕ} (a : DistinctTuple X r) : Set U :=
  Set.range (fun j => (a j).val)

end ActiveLanguageGeneration.Hierarchy



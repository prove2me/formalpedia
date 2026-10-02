-- Prove2me | Definitions.Def_opg37364_lps13_words
-- name    : opg37364_lps13_words
-- status  : Definition
-- author  : @arexychen
-- created : 2026-09-10T12:12:10.467677+00:00
-- url     : https://prove2.me/theorems/77a04587-70b5-46db-8d8b-6779052a1acb
-- title:
--   Ordered quaternion words and adjacent reducedness for LPS13
-- statement:
--   Let α_s, for s∈{0,…,13}, be precisely the existing fourteen integral norm-13 quaternion generators, and let bar(s) be their existing conjugate-index involution. For a finite word w=(s₁,…,sₘ), define its ordered quaternion product by
--
--   $$Q(w)=α_{s_1}\cdots α_{s_m},\qquad Q(\varnothing)=1.$$
--
--   A word is reduced exactly when s_{j+1}≠bar(s_j) for every adjacent pair. The empty and one-letter words are reduced. This imposes neither cyclic reduction nor pairwise distinctness; repeated noninverse letters are allowed. These two definitions contain no primitivity, nonvanishing, freeness, normal-form, connectedness or girth assumption.
-- source:
--   DSV, Elementary Number Theory, Group Theory, and Ramanujan Graphs, Definition 2.6.12 and Theorem 2.6.13, specialized to the existing fixed-p=13 generator convention. https://math.bme.hu/~gabor/oktatas/SztoM/DavidoffSarnakValette.pdf . Only ordered words and adjacent reducedness are defined here; no factorization theorem is assumed.

import Definitions.Def_opg37364_lps13

set_option autoImplicit false

namespace OPG37364

/-- Ordered product of the original integral norm-13 quaternion generators.
The empty word has product 1. -/
def lps13WordProduct (w : List (Fin 14)) : Quaternion ℤ :=
  (w.map lps13Quaternion).prod

/-- Only adjacent conjugate pairs are forbidden; no cyclic or pairwise condition. -/
def lps13WordReduced : List (Fin 14) → Prop
  | [] => True
  | [_] => True
  | a :: b :: tail => b ≠ lps13ConjIndex a ∧ lps13WordReduced (b :: tail)

end OPG37364



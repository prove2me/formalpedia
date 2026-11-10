-- Prove2me | Definitions.Def_StudentTeacher976_Adaptivity_Refutable
-- name    : StudentTeacher976_Adaptivity_Refutable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T10:10:14.110839+00:00
-- url     : https://prove2.me/theorems/6a5982ff-21cc-4c4f-81f7-cc9082e56772
-- title:
--   Total polynomially bounded refutable search presentations (Definition 1.1)
-- statement:
--   Fix $i\ge0$ and a relation $R$ on pairs of finite binary strings. A refutable presentation supplies polynomials $a,b$ and a predicate $\varphi\in\Delta_{i+1}^p$. It asserts totality, bounds every permitted answer by $a(|x|)$, and links the same underlying relation to the predicate by
--
--   $$
--   R(x,y)\ \Longleftrightarrow\ \forall z\in\{0,1\}^{b(|x|)}\;\varphi(x,y,z).
--   $$
--
--   Every input string has an answer, including the empty input. The predicate's language contains exactly the well-encoded triples satisfying it, so malformed triple encodings are rejected by its decision procedure. Exact refutation lengths use padding.
--
--   A presentation is the common interface between the search relation and its Student–Teacher game. Boundedness, totality, and refutability all refer to $R$, rather than to unrelated predicates.
-- source:
--   Ondřej Ježil, Dimitrios Tsintsilidas, STOC 2027 submission #976 (October 2026), Definition 1.1, p.6 (PDF p.6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_Complexity

open QAdvFew.PoQOracle

namespace StudentTeacher976.Adaptivity

/-- Definition 1.1, p.6. A presentation of the underlying total, polynomially bounded
relation R; the same R occurs in the boundedness, totality and representation clauses.
Exact refutation length is a padding convention. Predicate evaluation rejects malformed
triple encodings, as specified by the language in the efficiency field. -/
structure RefutablePresentation (i : ℕ) (R : SearchRelation) where
  answerBound : Polynomial ℕ
  refutationLength : Polynomial ℕ
  test : Word → Word → Word → Prop
  efficient : {s | ∃ x y z, s = tup [x, y, z] ∧ test x y z} ∈ Delta i
  total : ∀ x, ∃ y, R x y
  bounded : ∀ x y, R x y → y.length ≤ answerBound.eval x.length
  represents : ∀ x y, R x y ↔ ∀ z,
    z.length = refutationLength.eval x.length → test x y z

end StudentTeacher976.Adaptivity



-- Prove2me | Definitions.Def_TetrisHard_Rows_Search
-- name    : TetrisHard_Rows_Search
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T22:50:26.536729+00:00
-- url     : https://prove2.me/theorems/e272e9f0-efd2-4161-a37a-360072dd34a6
-- title:
--   Finite-string search problems and polynomial-time reductions
-- statement:
--   A search problem consists of a set of valid binary queries and a relation between queries and binary answers. NP-hardness means that every NP language over every finite nonempty alphabet admits polynomial-time query and answer transformations. The query is valid for every input; every answer allowed by the search relation lets the answer transformation decide membership in the original language. The answer map receives both the original input and oracle answer in a tagged, separated string. Both transformations use the published Cook Turing-machine runtime definition, not output-size bounds. This generic interface is independent of Tetris. The relation need not be total: a factor below one can admit no approximation answer on positive-optimum instances.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Theorem 6.5, p. 21; computational encoding of NP-hard approximation, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_CookPvsNP_defs

namespace TetrisHard.Rows

/-- A finite-string search relation, independent of any particular optimization problem. -/
structure SearchProblem where
  valid : List Bool → Prop
  answer : List Bool → List Bool → Prop

/-- Polynomial-time instance and answer transformations. Correctness holds for every
permitted answer, not only for a selected solution. Runtime is Cook's machine runtime. -/
def SearchProblem.NPHard (S : SearchProblem) : Prop :=
  ∀ (Α : Type) [Fintype Α] [Nonempty Α] (L : CookPvsNP.Lang Α), L ∈ CookPvsNP.NP Α →
    ∃ (query : List Α → List Bool)
      (decode : List (Option (Α ⊕ Bool)) → List Bool),
      CookPvsNP.PolyTimeComputable query ∧ CookPvsNP.PolyTimeComputable decode ∧
      ∀ x, S.valid (query x) ∧ ∀ y, S.answer (query x) y →
        (x ∈ L ↔ decode (x.map (some ∘ Sum.inl) ++ none :: y.map (some ∘ Sum.inr)) = [true])

end TetrisHard.Rows



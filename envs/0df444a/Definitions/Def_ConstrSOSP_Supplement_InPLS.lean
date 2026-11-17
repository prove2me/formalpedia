-- Prove2me | Definitions.Def_ConstrSOSP_Supplement_InPLS
-- name    : ConstrSOSP_Supplement_InPLS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:27:01.539541+00:00
-- url     : https://prove2.me/theorems/333502b1-7363-4e73-8028-b6806c9a9a36
-- title:
--   Membership in PLS: polynomial-time checkable and reducible to LocalOpt
-- statement:
--   A search problem $P$ **lies in PLS** when
--
--   1. its answers are checkable in polynomial time: some polynomial-time computable function, given an instance $s$ and a candidate $t$, accepts exactly when $t$ is an answer of $P$ on $s$, for every valid instance $s$; and
--   2. $P$ reduces to LocalOpt by a polynomial-time search reduction, correct for every LocalOpt answer.
--
--   This follows the paper's definition: "PLS is traditionally defined as the complexity class which contains all TFNP problems that reduce to the PLS-complete Localopt problem". Totality on valid instances follows from (2), because LocalOpt is total.
--
--   **Formalization Note** The pair $(s,t)$ is given to the checker as one string with a separator, so its running time is polynomial in $|s|+|t|$. Polynomial time is `CookPvsNP.PolyTimeComputable`; reductions are `CardinalMatching.SearchReduces`.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_ConstrSOSP_LocalOpt

namespace ConstrSOSP.Supplement

open ConstrSOSP

/-- **Membership in PLS** (Kontogiannis, Panageas & Pollatos, arXiv:2604.02285, 2 Nov 2026, §4.1,
p.17: "PLS is traditionally defined as the complexity class which contains all TFNP problems that
reduce to the PLS-complete Localopt problem").

`InPLS P` holds iff
1. the answers of `P` are checkable in polynomial time on valid instances: some function `V`,
   polynomial-time computable on Cook's Turing machines (`CookPvsNP.PolyTimeComputable`), outputs
   `[true]` on the pair `(s, t)` exactly when `t` is an answer of `P` on `s`, for every valid `s`;
   and
2. `P` reduces to LocalOpt by a polynomial-time search reduction (`CardinalMatching.SearchReduces`,
   correct for every LocalOpt answer).

**Formalization Note** The pair `(s, t)` is written over `Option (Bool ⊕ Bool)` as
`s.map (some ∘ inl) ++ none :: t.map (some ∘ inr)`, the pairing of `SearchReduces`, so the
checker's time is polynomial in `|s| + |t|`. Totality of `P` on valid instances follows from (2),
since LocalOpt is total. -/
def InPLS (P : TetrisHard.Rows.SearchProblem) : Prop :=
  (∃ V : List (Option (Bool ⊕ Bool)) → List Bool, CookPvsNP.PolyTimeComputable V ∧
    ∀ s, P.valid s → ∀ t,
      (V (s.map (some ∘ Sum.inl) ++ none :: t.map (some ∘ Sum.inr)) = [true] ↔ P.answer s t)) ∧
  CardinalMatching.SearchReduces P LocalOpt

end ConstrSOSP.Supplement



-- Prove2me | Definitions.Def_CardinalMatching_SearchReduces
-- name    : CardinalMatching_SearchReduces
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:51.736989+00:00
-- url     : https://prove2.me/theorems/c2674294-d341-4344-9085-a74f1c3928f4
-- title:
--   Polynomial-time search reduction $Q\le_p R$
-- statement:
--   A **search problem** consists of a validity predicate on bit strings (the instances) and an answer relation between instances and bit strings. A **polynomial-time search reduction** from $Q$ to $R$ is a pair of maps, both computable in polynomial time on Cook's Turing machines:
--
--   1. an instance map $f$ such that $f(s)$ is a valid instance of $R$ for every valid instance $s$ of $Q$;
--   2. an answer map $g$ such that for every valid $s$ and **every** answer $t$ of $R$ on $f(s)$, $g(s,t)$ is an answer of $Q$ on $s$.
--
--   The map $g$ reads the original instance together with the answer, so its running time is polynomial in $|s|+|t|$. These are the reductions under which PPAD-hardness is defined.
--
--   **Formalization Note** The paper does not define its reductions; this is the standard Levin reduction for total search problems. The pair $(s,t)$ is written with a separator symbol. Search problems are the public `TetrisHard.Rows.SearchProblem`, and polynomial-time computability is the public `CookPvsNP.PolyTimeComputable`.
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Theorems 8 and 9, p.6, and proof of Theorem 8, p.14 (reductions are not defined in the paper)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_TetrisHard_Rows_Search

namespace CardinalMatching

/-- **Polynomial-time search reduction** `Q ≤ₚ R` between finite-string search problems (the
reductions behind "PPAD-hard" in Tröbst–Vazirani, *Cardinal-Utility Matching Markets*,
arXiv:2402.08851v6, Theorems 8 and 9, p.6, and the proof of Theorem 8, p.14: "we can construct
(x̂, p̂) … in polynomial time"). There are an instance map `f` and an answer map `g`, both
polynomial-time computable on Cook's Turing machines, such that for every valid instance `s` of
`Q`, `f s` is a valid instance of `R`, and for **every** answer `t` of `R` on `f s`, `g` applied
to the pair `(s, t)` is an answer of `Q` on `s`.

**Formalization Note** The paper does not define its reductions; this is the standard (Levin)
search reduction used for PPAD. The pair `(s, t)` is written over the alphabet
`Option (Bool ⊕ Bool)` as `s.map (some ∘ inl) ++ none :: t.map (some ∘ inr)` (the separator
`none`), so the running time of `g` is polynomial in `|s| + |t|`. Correctness is required for
every answer of `R`, not for one selected answer. Search problems are the public
`TetrisHard.Rows.SearchProblem` (a validity predicate and an answer relation on `List Bool`), and
`PolyTimeComputable` is the public `CookPvsNP.PolyTimeComputable`. -/
def SearchReduces (Q R : TetrisHard.Rows.SearchProblem) : Prop :=
  ∃ (f : List Bool → List Bool) (g : List (Option (Bool ⊕ Bool)) → List Bool),
    CookPvsNP.PolyTimeComputable f ∧ CookPvsNP.PolyTimeComputable g ∧
    ∀ s, Q.valid s → R.valid (f s) ∧
      ∀ t, R.answer (f s) t →
        Q.answer s (g (s.map (some ∘ Sum.inl) ++ none :: t.map (some ∘ Sum.inr)))

end CardinalMatching



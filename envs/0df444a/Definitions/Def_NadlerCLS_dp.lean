-- Prove2me | Definitions.Def_NadlerCLS_dp
-- name    : NadlerCLS_dp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:52:02.78036+00:00
-- url     : https://prove2.me/theorems/6e47158d-c108-40d8-b767-77f7caffdea0
-- title:
--   The ultrametric $d_p$ of a potential
-- statement:
--   For a set $X$ and a potential $p:X\to\mathbb R$,
--   $$ d_p(x,y)=\begin{cases}0,&x=y,\\ 1+\max\{p(x),p(y)\},&x\ne y.\end{cases} $$
--   This is (C.8), the metric of the hardness reduction (Lemma C.8): the local-search potential is encoded into the metric, and the update map becomes a singleton correspondence.
--
--   **Formalization Note** Defined on an arbitrary type, with classical equality.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), proof of Lemma C.8, Eq. (C.8), p.38

import Mathlib

set_option autoImplicit false

namespace NadlerCLS

/-- The **ultrametric `d_p` built from a potential** (Xiong–Vlatakis-Gkaragkounis, *On the
Complexity of Finding Fixed Points for Set-Valued Contractions*, arXiv:2609.14101, held version of
2026-11-03, sha256 1fcc5a02…6dc485, proof of Lemma C.8, Eq. (C.8), p.38):
`d_p(x, y) = 0` if `x = y`, and `d_p(x, y) = 1 + max{p(x), p(y)}` if `x ≠ y`.

**Formalization Note** Defined on an arbitrary type `α` (the paper's `X = [0, 1]ⁿ`), with
classical equality. -/
noncomputable def dp {α : Type*} (p : α → ℝ) (x y : α) : ℝ := by
  classical
  exact if x = y then 0 else 1 + max (p x) (p y)

end NadlerCLS



-- Prove2me | Definitions.Def_DerandSq_wordOp
-- name    : DerandSq_wordOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:56:43.306206+00:00
-- url     : https://prove2.me/theorems/4c4a2788-deed-489c-bd11-2376c3bb6b30
-- title:
--   Words evaluated at operators
-- statement:
--   A word $w = \ell_1 \ell_2 \cdots \ell_n$ in the letters $x_i, x_i^*$ evaluated at a tuple $u$ of bounded operators is the product $w(u) = \ell_1(u)\,\ell_2(u) \cdots \ell_n(u)$ of its evaluated letters in the order they appear; the empty word is the identity.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), §2.4, p.12

import Mathlib
import Definitions.Def_DerandSq_letterOp

namespace DerandSq

/-- A word in the letters `x_i, x_i*` evaluated at a tuple `u` of bounded operators: the product
of its letters in the order they appear (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), §2.4, p.12). -/
noncomputable def wordOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} (u : ι → E →L[ℂ] E) (w : FreeMonoid (ι ⊕ ι)) : E →L[ℂ] E :=
  (w.toList.map (letterOp u)).prod

end DerandSq



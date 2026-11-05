-- Prove2me | Definitions.Def_DotySW_Deranged_slotSplit
-- name    : DotySW_Deranged_slotSplit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:31.61595+00:00
-- url     : https://prove2.me/theorems/0b7f39e6-2f79-463b-ab37-3cf7b419e726
-- title:
--   The summand of $\mathfrak{gl}_n^{\otimes r}$ with $\mathfrak{sl}_n$ in the slots of $S$
-- statement:
--   For a set $S$ of slots, this is the span of the pure tensors $X_0\otimes\cdots\otimes X_{r-1}$ with $X_a$ traceless for $a\in S$ and $X_a$ a scalar matrix for $a\notin S$. These are the summands obtained by expanding $\mathfrak{gl}_n=\mathfrak{sl}_n\oplus\mathbb C$ in every slot of $\mathfrak{gl}_n^{\otimes r}$.
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §4.2, Eq. (16), p. 10

import Mathlib
import Definitions.Def_DotySW_Deranged_pureGl

namespace DotySW.Deranged

/-- **The summand of `gl_n^{⊗r}` with `sl_n` in the slots of `S` and `ℂ` elsewhere.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §4.2, Eq. (16), p. 10.

Expanding `gl_n = sl_n ⊕ ℂ` in every slot gives one summand for each subset `S` of the slots: the
span of the pure tensors with a traceless matrix in the slots of `S` and a scalar matrix in the
others. -/
def slotSplit (n r : ℕ) (S : Finset (Fin r)) : Submodule ℂ (Idx n (r + r) → ℂ) :=
  Submodule.span ℂ {w | ∃ X : Fin r → Matrix (Fin n) (Fin n) ℂ,
    (∀ a ∈ S, (X a).trace = 0) ∧ (∀ a, a ∉ S → ∃ c : ℂ, X a = c • 1) ∧ w = pureGl n r X}

end DotySW.Deranged



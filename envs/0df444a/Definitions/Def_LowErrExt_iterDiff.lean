-- Prove2me | Definitions.Def_LowErrExt_iterDiff
-- name    : LowErrExt_iterDiff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:18.194688+00:00
-- url     : https://prove2.me/theorems/35c62030-0d31-44b3-86ea-675a76629d8b
-- title:
--   Iterated differences $2^{t-1}\mathbf X-2^{t-1}\mathbf X$ and $2^{t-1}V-2^{t-1}V$
-- statement:
--   Let $G$ be an abelian group. For a source $\mathbf X$ on $G$, $\mathbf X-\mathbf X$ denotes the difference of two independent copies. The **iterated difference** is defined by
--   $$2^{-1}\mathbf X-2^{-1}\mathbf X:=\mathbf X,\qquad 2^{t}\mathbf X-2^{t}\mathbf X:=\mathbf W-\mathbf W\ \text{ for }\ \mathbf W=2^{t-1}\mathbf X-2^{t-1}\mathbf X,$$
--   which, in an abelian group, is the law of the sum of $2^t$ independent copies of $\mathbf X$ minus the sum of $2^t$ further independent copies. The same recursion on sets gives $2^{t-1}V-2^{t-1}V$, with $\tfrac12V-\tfrac12V:=V$.
--
--   **Formalization Note** `iterDiff t X` is $2^{t-1}\mathbf X-2^{t-1}\mathbf X$; in particular `iterDiff 0 X = X` (the paper's convention $\tfrac12\mathbf X-\tfrac12\mathbf X:=\mathbf X$), not $\mathbf X-\mathbf X$.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), p.8 footnote 5, p.45, p.69

import Mathlib
import Definitions.Def_LowErrExt_indepPair

open Pointwise

namespace LowErrExt

/-- **Difference of two independent copies.** `diffLaw X` is the law of `X₁ − X₂` with `X₁, X₂`
independent copies of `X`.
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…), p.69:
"Recall we use the notation Y − Y to mean the difference of two independent copies of Y". -/
noncomputable def diffLaw {G : Type*} [AddCommGroup G] (X : PMF G) : PMF G :=
  (indepPair X X).map fun p => p.1 - p.2

/-- **Iterated differences `2^{t−1}X − 2^{t−1}X`.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…), p.8
footnote 5 ("2^tX denote the sum of 2^t independent copies of X") and p.45 ("recalling our notation
that ½X − ½X := X").

`iterDiff t X` is the law of `2^{t−1}X − 2^{t−1}X`: `iterDiff 0 X = X`, and `iterDiff (t+1) X` is
the difference of two independent copies of `iterDiff t X`.

**Formalization Note.** In an abelian group the difference of two independent copies of
`2^{t−1}X − 2^{t−1}X` has the law of the sum of `2^t` independent copies minus the sum of `2^t`
further independent copies, which is `2^tX − 2^tX`. The case `t = 0` is the paper's convention
`½X − ½X := X`, not `X − X`. -/
noncomputable def iterDiff {G : Type*} [AddCommGroup G] : ℕ → PMF G → PMF G
  | 0, X => X
  | t + 1, X => diffLaw (iterDiff t X)

/-- **Iterated difference sets `2^{t−1}V − 2^{t−1}V`.** `iterDiffSet 0 V = V` (the convention
`½V − ½V := V`, p.45) and `iterDiffSet (t+1) V = W − W` for `W = iterDiffSet t V`, pointwise. -/
def iterDiffSet {G : Type*} [AddCommGroup G] : ℕ → Set G → Set G
  | 0, V => V
  | t + 1, V => iterDiffSet t V - iterDiffSet t V

end LowErrExt



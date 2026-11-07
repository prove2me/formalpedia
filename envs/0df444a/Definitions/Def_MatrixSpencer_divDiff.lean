-- Prove2me | Definitions.Def_MatrixSpencer_divDiff
-- name    : MatrixSpencer_divDiff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:05.394242+00:00
-- url     : https://prove2.me/theorems/c3d124da-f7e7-4757-afe9-ee2ca4120a8f
-- title:
--   The divided difference $f'^{[1]}$
-- statement:
--   The divided difference of $f'$:
--   $$f'^{[1]}(x,y)=\begin{cases}\dfrac{f'(x)-f'(y)}{x-y},& x\ne y,\\[1ex] f''(x),& x=y.\end{cases}$$
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma C.1, p.27

import Mathlib

namespace MatrixSpencer

/-- **The divided difference `f′^[1]` of `f′`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma C.1, p.27: "f′^[1](x, y) = (f′(x) − f′(y))/(x − y) for x ≠ y, and f′′(x) for x = y".

**Formalization Note.** `f′` and `f″` are `deriv f` and `deriv (deriv f)`. They are read at points of
the open interval on which `f` is `C²`, so Lean's junk derivative is not read. -/
noncomputable def divDiff (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  open Classical in
  if x = y then deriv (deriv f) x else (deriv f x - deriv f y) / (x - y)

end MatrixSpencer



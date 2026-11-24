-- Prove2me | Definitions.Def_MonotoneCompStatics_QSMChar_Supplement_RichFamily
-- name    : MonotoneCompStatics_QSMChar_Supplement_RichFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T04:06:05.826556+00:00
-- url     : https://prove2.me/theorems/f883f42a-a62f-411f-844c-2db223ad89b9
-- title:
--   Richly parameterized families
-- statement:
--   Let $A$ be an arbitrary index type and let $h_a:\mathbb R\to\mathbb R$ be a family. It is richly parameterized when
--   $$x\ne x'\ \Longrightarrow\ \exists a\in A:\quad h_a(x)=y,\quad h_a(x')=y'$$
--   for all real $x,y,x',y'$. No continuity or monotonicity of the individual functions is assumed. This is the family condition used in dissection.
-- source:
--   Milgrom and Shannon, Monotone Comparative Statics, Econometrica 62 (1994), DOI 10.2307/2951479, p.167, PDF 12, definition preceding Theorem 11

import Mathlib

namespace MonotoneCompStatics.QSMChar.Supplement

def RichFamily {A : Type*} (h : A → ℝ → ℝ) : Prop :=
  ∀ x y x' y' : ℝ, x ≠ x' → ∃ a : A, h a x = y ∧ h a x' = y'

end MonotoneCompStatics.QSMChar.Supplement



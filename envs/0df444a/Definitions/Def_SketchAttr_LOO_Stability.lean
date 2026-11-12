-- Prove2me | Definitions.Def_SketchAttr_LOO_Stability
-- name    : SketchAttr_LOO_Stability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:28:21.178705+00:00
-- url     : https://prove2.me/theorems/8c272918-16dd-4133-a7f7-8bf5bf40d73b
-- title:
--   Definition 4.5 — Taylor-tensor stability
-- statement:
--   Let $f:\mathbb C^n\to\mathbb C$ be an arithmetic circuit and let $\alpha:(0,\infty)\to[0,\infty]$ be a profile. The circuit is $\alpha$-stable when its normalized Taylor tensors satisfy
--   $$\|T_f^{(r)}\|_F\le\frac{\alpha(B)}{B^r}\qquad\text{for every }B>0\text{ and integer }r\ge1.$$
--   The norm is the Frobenius norm of the symmetric tensor, including all ordered entries. No real-coefficient condition is included. Accuracy statements require finiteness at their particular profile argument, such as $\alpha(4)<\infty$.
--
--   This condition controls coefficient decay uniformly over every degree and every positive radius. **Formalization Note** The profile takes values in extended nonnegative reals, and its domain is the subtype of positive real numbers. The function-level predicate is used only on circuit polynomials in the theorems.
-- source:
--   Liaw, Mehta, Velegkas, Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2), p. 12, Definition 4.5; canonical PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/9.pdf

import Mathlib
import Definitions.Def_SketchAttr_LOO_Taylor
open scoped ENNReal

namespace SketchAttr.LOO

abbrev StabilityProfile := {B : ℝ // 0 < B} → ℝ≥0∞

def IsStable {n : ℕ} (f : Vec n → ℂ) (α : StabilityProfile) : Prop :=
  ∀ (B : {B : ℝ // 0 < B}) (r : ℕ), 1 ≤ r →
    ENNReal.ofReal (frobNorm (taylorTensor f r)) ≤ α B / ENNReal.ofReal (B.val ^ r)

end SketchAttr.LOO



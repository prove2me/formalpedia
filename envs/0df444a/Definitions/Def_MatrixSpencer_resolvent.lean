-- Prove2me | Definitions.Def_MatrixSpencer_resolvent
-- name    : MatrixSpencer_resolvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:02.200348+00:00
-- url     : https://prove2.me/theorems/3e40ea61-ec9d-429f-874e-ee7838222841
-- title:
--   The resolvent $R=(I-X)^{-1}$
-- statement:
--   The resolvent $R=(I-X)^{-1}$ of a matrix $X$. It is applied at matrices with $\|X\|<1$, where it exists.
--
--   **Formalization Note** Elsewhere the Lean inverse is a junk value, which is only ever multiplied by the weight $w=0$.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.6, p.8

import Mathlib

namespace MatrixSpencer

/-- **The resolvent `R = (I − X)⁻¹`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Lemma 2.6, p.8, and Step 3 of the proof of Theorem 2.5, p.10.

**Formalization Note.** On `‖X‖ < 1` the matrix `I − X` is invertible. Elsewhere Lean's inverse is a
junk value, which is only ever multiplied by `weight`, equal to `0` there. -/
noncomputable def resolvent {d : ℕ} (X : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (1 - X)⁻¹

end MatrixSpencer



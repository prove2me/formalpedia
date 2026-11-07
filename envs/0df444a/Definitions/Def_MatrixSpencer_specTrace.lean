-- Prove2me | Definitions.Def_MatrixSpencer_specTrace
-- name    : MatrixSpencer_specTrace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:58.780821+00:00
-- url     : https://prove2.me/theorems/d0406863-98bd-4bbf-b86f-d4450828950c
-- title:
--   The spectral trace $\mathrm{Tr}\,f(X)$
-- statement:
--   For a real symmetric $d\times d$ matrix $X$ with eigenvalues $\lambda_1,\dots,\lambda_d$ and a function $f$, the spectral trace
--   $$\mathrm{Tr}\,f(X)=\sum_{a=1}^d f(\lambda_a).$$
--
--   **Formalization Note** The sum runs over the roots, with multiplicity, of the characteristic polynomial. For a real symmetric matrix this polynomial splits over $\mathbb R$, so these are exactly the eigenvalues. The function is only read at symmetric matrices.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.2, p.8; Lemma C.1, p.27

import Mathlib

namespace MatrixSpencer

/-- **The spectral trace `Tr f(X) = ∑ₐ f(λₐ(X))`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.2, p.8 ("V(X) = Tr v(X)") and Lemma C.1, p.27 ("Tr f(B)").

**Formalization Note.** The sum over the eigenvalues, with multiplicity, is the sum over the roots
of the characteristic polynomial. A real symmetric matrix has `d` real eigenvalues, so its
characteristic polynomial splits and no eigenvalue is lost; this form needs no symmetry proof as an
argument. It is only read at symmetric matrices. It is checked on diagonal matrices in
`Solutions/verification/MatrixSpencer_sanity.lean`. -/
noncomputable def specTrace {d : ℕ} (f : ℝ → ℝ) (X : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  (X.charpoly.roots.map f).sum

end MatrixSpencer



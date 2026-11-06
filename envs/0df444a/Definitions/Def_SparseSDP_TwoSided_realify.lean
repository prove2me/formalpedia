-- Prove2me | Definitions.Def_SparseSDP_TwoSided_realify
-- name    : SparseSDP_TwoSided_realify
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:00.747198+00:00
-- url     : https://prove2.me/theorems/86944645-454c-4813-afab-e0bfeea92405
-- title:
--   Realification $\Phi$, its inverse map $\Psi$, and the realified instance
-- statement:
--   For $A\in\mathbb C^{n\times n}$ and a real $2n\times2n$ matrix $Y$ with blocks $Y_{ab}$,
--   $$
--   \Phi(A)=\begin{pmatrix}\mathrm{Re}\,A&-\mathrm{Im}\,A\\\mathrm{Im}\,A&\mathrm{Re}\,A\end{pmatrix},\qquad
--   \Psi(Y)=Y_{11}+Y_{22}+i(Y_{21}-Y_{12}),
--   $$
--   Eqs. (369), (372). The realified instance replaces every matrix by its realification and keeps the thresholds (Eqs. (375), (376)).
--
--   The stochastic solver is analyzed for real symmetric matrices, and this map carries Hermitian inputs to it.
--
--   **Formalization Note** The block index $\mathrm{Fin}\,n\oplus\mathrm{Fin}\,n$ is reindexed to $\mathrm{Fin}(n+n)$ by `finSumFinEquiv`, so the first block comes first.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Appendix A, Eqs. (369), (372), (375), (376), p. 67

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Instance

open Matrix

namespace SparseSDP.TwoSided

variable {n m : ℕ}

/-- The realification `Φ(A) = (Re A, −Im A; Im A, Re A)`, Eq. (369), p. 67, with the block index
`Fin n ⊕ Fin n` reindexed to `Fin (n + n)`. -/
noncomputable def realify (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  reindex finSumFinEquiv finSumFinEquiv
    (fromBlocks (A.map Complex.re) (-(A.map Complex.im)) (A.map Complex.im) (A.map Complex.re))

/-- `Ψ(Y) = Y₁₁ + Y₂₂ + i(Y₂₁ − Y₁₂)`, Eq. (372), p. 67. -/
noncomputable def derealify (Y : Matrix (Fin (n + n)) (Fin (n + n)) ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  let B := reindex finSumFinEquiv.symm finSumFinEquiv.symm Y
  (B.toBlocks₁₁ + B.toBlocks₂₂).map (fun x : ℝ => (x : ℂ)) +
    Complex.I • (B.toBlocks₂₁ - B.toBlocks₁₂).map (fun x : ℝ => (x : ℂ))

/-- The realified instance of Eqs. (375), (376), p. 67: every matrix is replaced by its realification
and the thresholds are unchanged. -/
noncomputable def realInst (I : Instance ℂ n m) : Instance ℝ (n + n) m where
  C := realify I.C
  A := fun j => realify (I.A j)
  b := I.b

end SparseSDP.TwoSided



-- Prove2me | Definitions.Def_SpectralSparsify_Sampling_SpectralNotions
-- name    : SpectralSparsify_Sampling_SpectralNotions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:21.029998+00:00
-- url     : https://prove2.me/theorems/a192be5c-ca68-4079-8de7-8cf432ef3348
-- title:
--   D^{-1/2}, the normalized Laplacian ℒ_G = D^{-1/2}L_GD^{-1/2}, its smallest nonzero eigenvalue, and the 2-norm of a symmetric matrix
-- statement:
--   Let $G$ be an unweighted graph on a finite vertex set $V$, with degrees $d_v$, degree matrix $D=\operatorname{diag}(d_v)$ and Laplacian $L_G=D-A$. Write $D^{-1/2}$ for the diagonal matrix with entries $1/\sqrt{d_v}$. The **normalized Laplacian** of $G$ is
--   $$\mathcal L_G=D^{-1/2}L_GD^{-1/2}.$$
--
--   For a real square matrix $M$ indexed by $V$ and a real $\lambda$, "the smallest non-zero eigenvalue of $M$ is at least $\lambda$" means: every eigenvalue $\mu\neq 0$ of $M$, with eigenvector $f\neq 0$, satisfies $\mu\ge\lambda$.
--
--   For a symmetric real matrix $M$, the **2-norm** $\|M\|$ is the largest absolute value of its eigenvalues. Accordingly, $\|M\|\le t$ means every eigenvalue $\mu$ of $M$ has $|\mu|\le t$, and $\|M\|\ge t$ means some eigenvalue $\mu$ of $M$ has $|\mu|\ge t$.
--
--   These notions state the spectral hypothesis of Theorem 6.1 and Lemma 6.2 and the norm bounds of Lemmas 6.2, 6.3 and 6.7.
--
--   **Formalization Note** `degInvSqrt G` has entries `1 / √(d_v)`; it is $D^{-1/2}$ only when every degree is positive, and every statement using it assumes that ($\mathcal L_G$ is undefined otherwise). `normalize G M` is $D^{-1/2}MD^{-1/2}$ with $G$'s degrees. Eigenvalues are taken with real eigenvectors (`M.mulVec f = μ • f`, `f ≠ 0`); the norm predicates `NormLE`, `NormGE` are applied only to symmetric matrices, whose eigenvalues are real with real eigenvectors, so they are the 2-norm statements of footnote 2. The paper's $\lambda$ is written `lam` (`λ` is a Lean keyword).
-- source:
--   D. A. Spielman, S.-H. Teng, Spectral Sparsification of Graphs, arXiv:0808.4134v3, §4, p. 5 (normalized Laplacian); p. 8, footnote 2 (2-norm)

import Mathlib

namespace SpectralSparsify.Sampling

/-- `D^{-1/2}` for the unweighted graph `G`: the diagonal matrix with entries `1/√d_v`
(Spielman–Teng, arXiv:0808.4134v3, §4, p. 5). It is the inverse square root of `D` when every
degree is positive. -/
noncomputable def degInvSqrt {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Matrix V V ℝ :=
  Matrix.diagonal fun v => 1 / Real.sqrt (G.degree v)

/-- The congruence `M ↦ D^{-1/2} M D^{-1/2}` by `G`'s degree matrix. -/
noncomputable def normalize {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (M : Matrix V V ℝ) : Matrix V V ℝ :=
  degInvSqrt G * M * degInvSqrt G

/-- The normalized Laplacian `ℒ_G = D^{-1/2} L_G D^{-1/2}` (p. 5), with `L_G = D - A` Mathlib's
`SimpleGraph.lapMatrix`. -/
noncomputable def normLap {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Matrix V V ℝ :=
  normalize G (G.lapMatrix ℝ)

/-- "The smallest non-zero eigenvalue of `M` is at least `λ`" (written `lam`): every nonzero eigenvalue `μ` of `M`
(with a real eigenvector `f ≠ 0`) satisfies `lam ≤ μ` (`lam` stands for the paper's `λ`). -/
def NonzeroEigGE {V : Type*} [Fintype V] (M : Matrix V V ℝ) (lam : ℝ) : Prop :=
  ∀ (μ : ℝ) (f : V → ℝ), f ≠ 0 → M.mulVec f = μ • f → μ ≠ 0 → lam ≤ μ

/-- `‖M‖ ≤ t` for a symmetric real matrix `M`, whose 2-norm is the largest absolute value of its
eigenvalues (footnote 2, p. 8): every real eigenvalue `μ` of `M` has `|μ| ≤ t`. -/
def NormLE {V : Type*} [Fintype V] (M : Matrix V V ℝ) (t : ℝ) : Prop :=
  ∀ (μ : ℝ) (f : V → ℝ), f ≠ 0 → M.mulVec f = μ • f → |μ| ≤ t

/-- `‖M‖ ≥ t` for a symmetric real matrix `M` (footnote 2, p. 8): some real eigenvalue `μ` of `M`
has `t ≤ |μ|`. -/
def NormGE {V : Type*} [Fintype V] (M : Matrix V V ℝ) (t : ℝ) : Prop :=
  ∃ (μ : ℝ) (f : V → ℝ), f ≠ 0 ∧ M.mulVec f = μ • f ∧ t ≤ |μ|

end SpectralSparsify.Sampling



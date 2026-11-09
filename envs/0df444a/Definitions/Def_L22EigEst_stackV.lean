-- Prove2me | Definitions.Def_L22EigEst_stackV
-- name    : L22EigEst_stackV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:14:35.303435+00:00
-- url     : https://prove2.me/theorems/d7beec4a-9661-42e6-89bc-5eaf77970555
-- title:
--   The stacking matrix $V\in\mathbb R^{sn\times n}$ of Algorithm 2
-- statement:
--   For integers $s,n$, the matrix $V\in\mathbb R^{sn\times n}$ stacks $s$ copies of the identity $I_n$ vertically and rescales by $1/\sqrt s$:
--
--   $$V=\frac1{\sqrt s}\begin{pmatrix}I_n\\ \vdots\\ I_n\end{pmatrix}.$$
--
--   For symmetric $A$, Algorithm 2 runs Algorithm 1 on $VAV^\top\in\mathbb R^{sn\times sn}$, whose entries are $A_{ij}/s$. Each entry of $VAV^\top$ costs one query to $A$, and $VAV^\top$ satisfies the bounded row-norm property (Claim 3.2).
--
--   **Formalization Note** Rows are indexed by pairs $(k,i)$ (copy $k$, row $i$), so the paper's "$i\equiv l \pmod n$" becomes $l=(k,i)$. The module proves that $VAV^\top$ is symmetric.
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Algorithm 2 (Figure 2), p.12

import Mathlib
open Matrix

namespace L22EigEst

/-- **The stacking matrix `V`** of Algorithm 2 (Figure 2, p.12), Menand, Waingarten, STOC 2027
submission (manuscript sha256 b1f6adce…): "the matrix V ∈ ℝ^{sn×n} is given by stacking s copies of
I_n vertically and rescaling by 1/√s".

**Formalization Note.** The `sn` rows are indexed by `Fin s × Fin n`: row `l = (k, i)` is the
`i`-th row of the `k`-th copy, so "i ≡ l (mod n)" of the paper becomes `l.2 = i`. The matrix
`VAV⊺` of Algorithm 2 is `stackV s n * A * (stackV s n)ᵀ`. -/
noncomputable def stackV (s n : ℕ) : Matrix (Fin s × Fin n) (Fin n) ℝ :=
  fun l j => if l.2 = j then 1 / Real.sqrt s else 0

/-- `VAV⊺` is symmetric when `A` is. -/
theorem stackV_conj_isHermitian (s : ℕ) {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : (stackV s n * A * (stackV s n)ᵀ).IsHermitian := by
  have h := Matrix.isHermitian_mul_mul_conjTranspose (stackV s n) hA
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

end L22EigEst



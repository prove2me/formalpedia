-- Prove2me | Definitions.Def_SchattenSketch_Main_Spectral
-- name    : SchattenSketch_Main_Spectral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:56:45.350573+00:00
-- url     : https://prove2.me/theorems/85cf0e3e-28ce-491b-9db7-c029c525893a
-- title:
--   Operator and Frobenius norms through singular values, the tail nuclear norm $T_h$, the tail energy $F_h^2$ and $a_h=\sigma_{h+1}$
-- statement:
--   For $B\in\mathbb R^{d_1\times d_2}$ with singular values $\sigma_1(B)\ge\sigma_2(B)\ge\dots\ge 0$ (the square roots of the eigenvalues of $B^\top B$, extended by zeros past the dimension),
--   $$\|B\|_{op}=\sigma_1(B),\qquad \|B\|_F=\Bigl(\sum_i\sigma_i(B)^2\Bigr)^{1/2}.$$
--   For a square $A\in\mathbb R^{n\times n}$ and a cutoff $h\ge 0$, the **tail nuclear norm**, the **tail energy** and the **first tail singular value** of (3.2) are
--   $$T_h(A)=\sum_{i>h}\sigma_i(A),\qquad F_h(A)^2=\sum_{i>h}\sigma_i(A)^2,\qquad a_h=\sigma_{h+1}(A),$$
--   with $a_n=0$ and $T_h=F_h=0$ for $h\ge n$. If $A_h$ is a best rank-$h$ approximation (the first $h$ singular directions of $A$), the residual $A-A_h$ has singular values $\sigma_{h+1}(A)\ge\sigma_{h+2}(A)\ge\cdots$, so $T_h(A)=\|A-A_h\|_{S_1}$, $F_h(A)=\|A-A_h\|_F$ and $a_h=\|A-A_h\|_{op}$.
--
--   **Formalization Note.** Singular values are the published `singVal` (Mathlib's `LinearMap.singularValues`, 0-based): the paper's $\sigma_i$ is `singVal (i - 1)`, so $T_h$ is the sum of `singVal i A` over $h\le i<n$ and $a_h$ is `singVal h A`. The nuclear norm $\|A\|_{S_1}=\sum_i\sigma_i(A)$ is the published `nucNorm`.
-- source:
--   Lin F. Yang, Near-Optimal Bounds for Sketching the Schatten Norms, arXiv:2608.22247 (held version, sha256 c29a210a…), p. 4 (norms); p. 12, (3.2)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_singVal
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm

open WainwrightHDS.NucNorm

namespace SchattenSketch.Main

/-- Operator norm `‖B‖_op = σ₁(B)`, the largest singular value (Yang, p. 4). With the 0-based
`singVal`, the paper's `σ₁` is `singVal 0`. -/
noncomputable def opNorm {d₁ d₂ : ℕ} (B : Matrix (Fin d₁) (Fin d₂) ℝ) : ℝ :=
  singVal 0 B

/-- Frobenius norm `‖B‖_F = (∑ᵢ σᵢ(B)²)^{1/2}` (Yang, p. 4). -/
noncomputable def frobNorm {d₁ d₂ : ℕ} (B : Matrix (Fin d₁) (Fin d₂) ℝ) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.range (min d₁ d₂), singVal j B ^ 2)

/-- Tail nuclear norm `T_h(A) = ∑_{i > h} σᵢ(A)` of (3.2) (Yang, p. 12); singular values past
the dimension are zero, so `T_h(A) = 0` for `h ≥ n`. 0-based: `σᵢ = singVal (i - 1)`. -/
noncomputable def tailNuc {n : ℕ} (h : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i ∈ Finset.Ico h n, singVal i A

/-- Squared tail Frobenius norm `F_h(A)² = ∑_{i > h} σᵢ(A)²` of (3.2) (Yang, p. 12). -/
noncomputable def tailFrobSq {n : ℕ} (h : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i ∈ Finset.Ico h n, singVal i A ^ 2

/-- `a_h = σ_{h+1}(A)` of (3.2) (Yang, p. 12): the largest singular value of the exact residual
`A - A_h`; it is `0` for `h ≥ n`. 0-based: `singVal h A`. -/
noncomputable def tailTop {n : ℕ} (h : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  singVal h A

end SchattenSketch.Main



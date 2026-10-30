-- Prove2me | Definitions.Def_WainwrightHDS_NucNorm_traceInner
-- name    : WainwrightHDS_NucNorm_traceInner
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:24:50.709301+00:00
-- url     : https://prove2.me/theorems/6559fe16-f478-4642-a49b-b74146c8fb23
-- title:
--   Trace inner product $\langle\!\langle A,B\rangle\!\rangle=\operatorname{trace}(A^\top B)$
-- statement:
--   For real $d_1\times d_2$ matrices $A$ and $B$, the **trace inner product** is
--
--   $$
--   \langle\!\langle A,B\rangle\!\rangle \;:=\; \operatorname{trace}(A^\top B) \;=\; \sum_{j_1=1}^{d_1}\sum_{j_2=1}^{d_2} A_{j_1j_2}B_{j_1j_2}.
--   $$
--
--   It is the Euclidean inner product of the vectorized matrices, induces the Frobenius norm, and defines orthogonality and projections on the matrix space $\mathbb R^{d_1\times d_2}$ throughout the analysis of nuclear-norm regularization.
--
--   **Formalization Note** The definition is the double sum of entrywise products; indices are 0-based.
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, §10.1, p. 312 (PDF p. 332), Eq. (10.1)

import Mathlib

namespace WainwrightHDS.NucNorm

/-- **Trace inner product** `⟨⟨A, B⟩⟩ := trace(AᵀB) = Σ_{j₁} Σ_{j₂} A_{j₁j₂} B_{j₁j₂}` on `ℝ^{d₁×d₂}`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, §10.1, p. 312 (PDF p. 332), Eq. (10.1).

Formalization Note: written as the double sum of entrywise products (equal to `trace(AᵀB)`).
Indices are 0-based (`Fin d₁`, `Fin d₂`); the book's are `1, …, d₁` and `1, …, d₂`. -/
def traceInner {d₁ d₂ : ℕ} (A B : Matrix (Fin d₁) (Fin d₂) ℝ) : ℝ :=
  ∑ a, ∑ b, A a b * B a b

end WainwrightHDS.NucNorm



-- Prove2me | Definitions.Def_WainwrightHDS_NucNorm_frobSq
-- name    : WainwrightHDS_NucNorm_frobSq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:25:09.138935+00:00
-- url     : https://prove2.me/theorems/03e1a9b6-6ecb-4632-b72a-cd785fb12ae2
-- title:
--   Squared Frobenius norm $|||A|||_F^2=\sum_{j_1,j_2}A_{j_1j_2}^2$
-- statement:
--   For a real $d_1\times d_2$ matrix $A$, the squared **Frobenius norm** is
--
--   $$
--   |||A|||_F^2 \;=\; \sum_{j_1=1}^{d_1}\sum_{j_2=1}^{d_2} \big(A_{j_1j_2}\big)^2 \;=\; \langle\!\langle A,A\rangle\!\rangle .
--   $$
--
--   The Frobenius norm is the norm induced by the trace inner product, i.e. the Euclidean norm of the vectorized matrix; error bounds for matrix estimators are stated in its square.
--
--   **Formalization Note** The square is defined directly; $|||A|||_F$ itself is its nonnegative square root.
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, §10.1, p. 312 (PDF p. 332), text following Eq. (10.1)

import Mathlib

namespace WainwrightHDS.NucNorm

/-- **Squared Frobenius norm** `|||A|||_F² = Σ_{j₁} Σ_{j₂} (A_{j₁j₂})²`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, §10.1, p. 312 (PDF p. 332), the Frobenius norm induced by the trace inner product (10.1).

Formalization Note: the square of the norm is defined directly (no square root); `|||A|||_F` is
`Real.sqrt (frobSq A)`. Indices are 0-based. -/
def frobSq {d₁ d₂ : ℕ} (A : Matrix (Fin d₁) (Fin d₂) ℝ) : ℝ :=
  ∑ a, ∑ b, A a b ^ 2

end WainwrightHDS.NucNorm



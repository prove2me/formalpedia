-- Prove2me | Definitions.Def_WainwrightHDS_NucNorm_opNorm2
-- name    : WainwrightHDS_NucNorm_opNorm2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:26:19.800974+00:00
-- url     : https://prove2.me/theorems/14535ed7-ca63-4111-94d5-b5b24cc269e2
-- title:
--   $\ell_2$-operator norm $|||N|||_2=\sup_{\|z\|_2=1}\|Nz\|_2$ of a rectangular matrix
-- statement:
--   For $N\in\mathbb R^{d_1\times d_2}$, the **$\ell_2$-operator norm** (spectral norm) is
--
--   $$
--   |||N|||_2 \;:=\; \sup_{\|z\|_2=1} \|Nz\|_2 ,
--   $$
--
--   the supremum over unit vectors $z\in\mathbb R^{d_2}$ of the Euclidean norm of $Nz\in\mathbb R^{d_1}$. It equals the largest singular value of $N$ and is the dual norm of the nuclear norm; the event $\mathbb G(\lambda_n)$ of Proposition 10.6 is stated in it.
--
--   **Formalization Note** The value is the operator norm of the continuous linear map $z\mapsto Nz$ between the Euclidean spaces $\mathbb R^{d_2}$ and $\mathbb R^{d_1}$ — not Mathlib's default entrywise sup norm on matrices and not the Frobenius norm. For $d_2=0$ it is $0$.
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, Exercise 9.4(c), p. 308 (PDF p. 328)

import Mathlib

namespace WainwrightHDS.NucNorm

/-- **The ℓ₂-operator (spectral) norm of a rectangular matrix**, `|||N|||₂ := sup_{‖z‖₂=1} ‖Nz‖₂`
for `N ∈ ℝ^{d₁×d₂}`. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, Exercise 9.4(c), p. 308 (PDF p. 328).

Formalization Note: the value is the operator norm of the continuous linear map `z ↦ N z` from
`EuclideanSpace ℝ (Fin d₂)` to `EuclideanSpace ℝ (Fin d₁)`. It is neither Mathlib's default
entrywise sup norm on matrices nor the Frobenius norm. When `d₂ = 0` (no unit vector `z`) the
value is `0`, the norm of the only (zero) map. -/
noncomputable def opNorm2 {d₁ d₂ : ℕ} (N : Matrix (Fin d₁) (Fin d₂) ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin N)‖

end WainwrightHDS.NucNorm



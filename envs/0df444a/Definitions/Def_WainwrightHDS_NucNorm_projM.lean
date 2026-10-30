-- Prove2me | Definitions.Def_WainwrightHDS_NucNorm_projM
-- name    : WainwrightHDS_NucNorm_projM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:30:48.982702+00:00
-- url     : https://prove2.me/theorems/7cd8420a-a919-4faa-aa80-d8b0e222da5d
-- title:
--   Projection $\Theta_{\mathbb M}=P_{\mathbb U}\Theta P_{\mathbb V}$
-- statement:
--   For subspaces $\mathbb U\subseteq\mathbb R^{d_1}$, $\mathbb V\subseteq\mathbb R^{d_2}$ and $\Theta\in\mathbb R^{d_1\times d_2}$, the projection of $\Theta$ onto $\mathbb M(\mathbb U,\mathbb V)$ is
--
--   $$
--   \Theta_{\mathbb M} \;:=\; P_{\mathbb U}\,\Theta\,P_{\mathbb V}.
--   $$
--
--   **Formalization Note** This is the trace-inner-product orthogonal projection (9.20) onto $\mathbb M(\mathbb U,\mathbb V)$, written as an explicit formula.
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, Eq. (10.15), p. 319 (PDF p. 339); projection (9.20), p. 269 (PDF p. 289)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_projMat

namespace WainwrightHDS.NucNorm

/-- **Projection onto `𝕄(𝕌, 𝕍)`**: `Θ_𝕄 := P_𝕌 Θ P_𝕍`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, (10.15), p. 319 (PDF p. 339) ("with the other terms defined similarly"), projections as in
(9.20).

Formalization Note: the Frobenius-orthogonal projection of `ℝ^{d₁×d₂}` onto `𝕄(𝕌, 𝕍)` is
`Θ ↦ P_𝕌 Θ P_𝕍`; the projection is defined by this formula. -/
noncomputable def projM {d₁ d₂ : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂))) (Θ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    Matrix (Fin d₁) (Fin d₂) ℝ :=
  projMat U * Θ * projMat V

end WainwrightHDS.NucNorm



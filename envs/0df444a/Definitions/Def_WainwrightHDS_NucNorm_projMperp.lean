-- Prove2me | Definitions.Def_WainwrightHDS_NucNorm_projMperp
-- name    : WainwrightHDS_NucNorm_projMperp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:31:34.525902+00:00
-- url     : https://prove2.me/theorems/c702d126-5ec7-4043-ac9d-021ca9b45c93
-- title:
--   Projection $\Theta_{\mathbb M^\perp}=\Theta-P_{\mathbb U}\Theta P_{\mathbb V}$
-- statement:
--   For subspaces $\mathbb U\subseteq\mathbb R^{d_1}$, $\mathbb V\subseteq\mathbb R^{d_2}$ and $\Theta\in\mathbb R^{d_1\times d_2}$, the projection of $\Theta$ onto the trace-orthogonal complement $\mathbb M^\perp(\mathbb U,\mathbb V)$ of the model subspace is
--
--   $$
--   \Theta_{\mathbb M^\perp} \;:=\; \Theta - P_{\mathbb U}\,\Theta\,P_{\mathbb V}.
--   $$
--
--   Its nuclear norm $|||\Theta^*_{\mathbb M^\perp}|||_{\mathrm{nuc}}$ is the approximation-error term of the cone constraint (10.15).
--
--   **Formalization Note** The identity minus the projection onto $\mathbb M(\mathbb U,\mathbb V)$.
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, Eq. (10.15), p. 319 (PDF p. 339); projection (9.20), p. 269 (PDF p. 289)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_projM

namespace WainwrightHDS.NucNorm

/-- **Projection onto `𝕄⊥(𝕌, 𝕍)`** (the trace-orthogonal complement of `𝕄(𝕌, 𝕍)`):
`Θ_{𝕄⊥} := Θ − P_𝕌 Θ P_𝕍`. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, (10.15), p. 319 (PDF p. 339), the term `|||Θ*_{𝕄⊥}|||_nuc`.

Formalization Note: identity minus the projection onto `𝕄(𝕌, 𝕍)` (`projM`); defined by this
formula. -/
noncomputable def projMperp {d₁ d₂ : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂))) (Θ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    Matrix (Fin d₁) (Fin d₂) ℝ :=
  Θ - projM U V Θ

end WainwrightHDS.NucNorm



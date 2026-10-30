-- Prove2me | Definitions.Def_WainwrightHDS_NucNorm_projMbarPerp
-- name    : WainwrightHDS_NucNorm_projMbarPerp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:29:26.48102+00:00
-- url     : https://prove2.me/theorems/c12f9001-13a2-41c2-a7eb-c9a250121c3e
-- title:
--   Projection $\Delta_{\overline{\mathbb M}^\perp}=P_{\mathbb U^\perp}\Delta P_{\mathbb V^\perp}$
-- statement:
--   For subspaces $\mathbb U\subseteq\mathbb R^{d_1}$, $\mathbb V\subseteq\mathbb R^{d_2}$ and $\Delta\in\mathbb R^{d_1\times d_2}$, the projection of $\Delta$ onto $\overline{\mathbb M}^\perp(\mathbb U,\mathbb V)$ is
--
--   $$
--   \Delta_{\overline{\mathbb M}^\perp} \;:=\; P_{\mathbb U^\perp}\,\Delta\,P_{\mathbb V^\perp},
--   $$
--
--   where $P_{\mathbb U^\perp}$, $P_{\mathbb V^\perp}$ are the matrices of the orthogonal projections onto $\mathbb U^\perp$, $\mathbb V^\perp$.
--
--   **Formalization Note** The book defines $\Delta_{\mathbb S}$ as the projection onto $\mathbb S$ in the trace inner product, $\arg\min_{\theta\in\mathbb S}\|\Delta-\theta\|$ (9.20). For $\mathbb S=\overline{\mathbb M}^\perp(\mathbb U,\mathbb V)$ this projection is the map $\Delta\mapsto P_{\mathbb U^\perp}\Delta P_{\mathbb V^\perp}$, which is the definition used here.
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, Eq. (10.15), p. 319 (PDF p. 339); projection (9.20), p. 269 (PDF p. 289)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_projMat

namespace WainwrightHDS.NucNorm

/-- **Projection onto `𝕄̄⊥(𝕌, 𝕍)`**: `Δ_{𝕄̄⊥} := P_{𝕌⊥} Δ P_{𝕍⊥}`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, (10.15), p. 319 (PDF p. 339): "Δ̂_𝕄̄ denotes the projection of the matrix Δ̂ onto the
subspace 𝕄̄, with the other terms defined similarly"; projections in the trace (Frobenius) inner
product as in (9.20).

Formalization Note: the Frobenius-orthogonal projection of `ℝ^{d₁×d₂}` onto `𝕄̄⊥(𝕌, 𝕍)` is
`Δ ↦ P_{𝕌⊥} Δ P_{𝕍⊥}` (it is self-adjoint and idempotent for the trace inner product and its
range is `𝕄̄⊥(𝕌, 𝕍)`); the projection is defined by this formula. -/
noncomputable def projMbarPerp {d₁ d₂ : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂))) (Δ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    Matrix (Fin d₁) (Fin d₂) ℝ :=
  projMat Uᗮ * Δ * projMat Vᗮ

end WainwrightHDS.NucNorm



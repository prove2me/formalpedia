-- Prove2me | Definitions.Def_WainwrightHDS_NucNorm_projMbar
-- name    : WainwrightHDS_NucNorm_projMbar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:30:18.790468+00:00
-- url     : https://prove2.me/theorems/635e8303-145c-4e22-8e08-600823f871f6
-- title:
--   Projection $\Delta_{\overline{\mathbb M}}=\Delta-P_{\mathbb U^\perp}\Delta P_{\mathbb V^\perp}$
-- statement:
--   For subspaces $\mathbb U\subseteq\mathbb R^{d_1}$, $\mathbb V\subseteq\mathbb R^{d_2}$ and $\Delta\in\mathbb R^{d_1\times d_2}$, the projection of $\Delta$ onto $\overline{\mathbb M}(\mathbb U,\mathbb V)$ is
--
--   $$
--   \Delta_{\overline{\mathbb M}} \;:=\; \Delta - P_{\mathbb U^\perp}\,\Delta\,P_{\mathbb V^\perp}.
--   $$
--
--   **Formalization Note** Since $\overline{\mathbb M}$ is the trace-orthogonal complement of $\overline{\mathbb M}^\perp$, its orthogonal projection (9.20) is the identity minus the projection onto $\overline{\mathbb M}^\perp$; the definition uses this formula.
-- source:
--   Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint, Cambridge University Press 2019, doi:10.1017/9781108627771, Eq. (10.15), p. 319 (PDF p. 339); projection (9.20), p. 269 (PDF p. 289)

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_projMbarPerp

namespace WainwrightHDS.NucNorm

/-- **Projection onto `𝕄̄(𝕌, 𝕍)`**: `Δ_{𝕄̄} := Δ − P_{𝕌⊥} Δ P_{𝕍⊥}`.
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, (10.15), p. 319 (PDF p. 339): "Δ̂_𝕄̄ denotes the projection of the matrix Δ̂ onto the
subspace 𝕄̄".

Formalization Note: `𝕄̄` is the trace-inner-product orthogonal complement of `𝕄̄⊥`, so the
orthogonal projection onto it is the identity minus the projection onto `𝕄̄⊥`
(`projMbarPerp`); the projection is defined by this formula. -/
noncomputable def projMbar {d₁ d₂ : ℕ} (U : Submodule ℝ (EuclideanSpace ℝ (Fin d₁)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin d₂))) (Δ : Matrix (Fin d₁) (Fin d₂) ℝ) :
    Matrix (Fin d₁) (Fin d₂) ℝ :=
  Δ - projMbarPerp U V Δ

end WainwrightHDS.NucNorm



-- Prove2me | Definitions.Def_LatentMixDRO_cvarObj
-- name    : LatentMixDRO_cvarObj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:41.415645+00:00
-- url     : https://prove2.me/theorems/c5393ebc-0163-4512-b9c4-e04237d98661
-- title:
--   CVaR dual objective of (7)
-- statement:
--   For a function $z$ of the covariates, a law $P_X$ and $\alpha_0>0$, the objective of the dual form (7) is
--
--   $$
--   g(\eta)=\frac1{\alpha_0}\,\mathbb E_{X\sim P_X}\big[(z(X)-\eta)_+\big]+\eta,\qquad\eta\in\mathbb R.
--   $$
--
--   Its infimum over $\eta$ is the conditional value-at-risk of $z(X)$ at level $\alpha_0$.
--
--   **Formalization Note** A Bochner integral: every theorem using this definition assumes that $z$ is integrable.
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, display (7), p.6

import Mathlib

open MeasureTheory

namespace LatentMixDRO

/-- The objective of the dual form (7): `η ↦ (1/α₀) E_{X∼P_X}[(z(X) - η)₊] + η`, the Rockafellar–Uryasev
function of the conditional value-at-risk of `z(X)`.

Duchi, Hashimoto & Namkoong, arXiv:2007.13982v2, display (7), p.6.

**Formalization Note.** A Bochner integral: the theorems using it supply integrability of `z`. -/
noncomputable def cvarObj {𝒳 : Type*} [MeasurableSpace 𝒳] (α₀ : ℝ) (PX : Measure 𝒳) (z : 𝒳 → ℝ)
    (η : ℝ) : ℝ :=
  (1 / α₀) * (∫ x, max (z x - η) 0 ∂PX) + η

end LatentMixDRO


